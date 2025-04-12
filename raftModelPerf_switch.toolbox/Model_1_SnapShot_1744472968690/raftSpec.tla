------------------------------ MODULE raftSpec ------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\* Modified by Ovidiu Marcu. Simplified model and performance invariants added.
\* Modified further to track message counts for entry commitment.
\* Modified further to incorporate HovercRaft changes.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS raftActionsSolution

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Check for term update first
       \/ UpdateTerm(i, j, m)
       \* Handle existing Raft message types
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m) \* HovercRaft updated logic
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)
       \* --- HovercRaft Additions: Handle Recovery Messages ---
       \/ /\ m.mtype = RecoveryRequest
          /\ HandleRecoveryRequest(i, j, m)
       \/ /\ m.mtype = RecoveryResponse
          /\ HandleRecoveryResponse(i, j, m)


\* Defines how the variables may transition.
Next ==
           \/ \E i \in Server : Timeout(i)
\*           \/ \E i \in Server : Restart(i)
           \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \* --- HovercRaft Changes: Client Interaction and Ordering ---
           \/ \E v \in Value : ClientMulticast(v) \* Simulate client sending payload via Switch
           \/ \E i \in Server, v \in Value : LeaderOrderRequest(i, v) \* Leader orders a received payload
           \* --- End HovercRaft Changes ---
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j) \* Sends HovercRaft metadata AppendEntries
           \/ \E m \in ValidMessage(messages) : Receive(m) \* Handles all message types via updated Receive
\*           \/ \E m \in ValidMessage(messages) : DuplicateMessage(m) \* Optional network behaviors
\*           \/ \E m \in ValidMessage(messages) : DropMessage(m)     \* Optional network behaviors

\* A restricted Next for targeted testing
MyNext ==
\*           \/ \E i \in Server : Timeout(i)
\*           \/ \E i \in Server : Restart(i)
\*           \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
\*           \/ \E i \in Server : BecomeLeader(i)
           \* --- HovercRaft Changes: Client Interaction and Ordering ---
           \/ \E v \in Value : ClientMulticast(v) \* Simulate client sending payload via Switch
           \/ \E i \in Server, v \in Value : LeaderOrderRequest(i, v) \* Leader orders a received payload
           \* --- End HovercRaft Changes ---
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j) \* Sends HovercRaft metadata AppendEntries
           \/ \E m \in {msg \in ValidMessage(messages) : \* Focus on HovercRaft message processing
                       msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse,
                                      RecoveryRequest, RecoveryResponse}} : Receive(m)
\*           \/ \E m \in ValidMessage(messages) : DuplicateMessage(m)
\*           \/ \E m \in ValidMessage(messages) : DropMessage(m)


\* The specification must start with the initial state and transition according
\* to Next. Implicitly uses 'vars' defined in raftVariables.
Spec == Init /\ [][Next]_vars

MySpec == MyInit /\ [][MyNext]_vars

\* -------------------- Invariants --------------------
\* These standard Raft invariants should still hold for HovercRaft,
\* as it aims to maintain the core safety properties.

\* At most one leader per term.
MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

\* If two logs contain an entry with the same index and term,
\* then the logs are identical in all preceding entries.
LogMatchingInv ==
    \A i, j \in Server : i /= j =>
        \A n \in 1..min(Len(log[i]), Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

\* If an entry is committed, it must be present in the logs of future leaders.
\* (Slightly adapted wording for checking prefixes against leader's log in its term)
LeaderCompletenessInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server : i /= j =>
            CheckIsPrefix(CommittedTermPrefix(j, currentTerm[i]),log[i])


\* Committed logs must be prefixes of one another.
LogInv ==
    \A i, j \in Server :
        \/ CheckIsPrefix(Committed(i),Committed(j))
        \/ CheckIsPrefix(Committed(j),Committed(i))

\* Note that LogInv checks for safety violations across space
\* This is a key safety invariant and should always be checked
THEOREM Spec => ([]LogInv /\ []LeaderCompletenessInv /\ []LogMatchingInv /\ []MoreThanOneLeaderInv)

=============================================================================
\* Created by Ovidiu-Cristian Marcu
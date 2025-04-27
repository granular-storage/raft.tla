---------------------------- MODULE raftActionsSolution ----------------------------

EXTENDS raftInit

----
\* Define state transitions

\* Modified to allow Restarts only for Leaders
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
\* Also persists messages and instrumentation vars elections, maxc, leaderCount, entryCommitStats
Restart(i) ==
    /\ state[i] = Leader \* limit restart to leaders todo mc
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars>>

\* Modified to restrict Timeout to just Followers
\* Server i times out and starts a new election. Follower -> Candidate
Timeout(i) == /\ state[i] \in {Follower} \*, Candidate
              /\ currentTerm[i] < MaxTerm
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars>>

\* Modified to restrict Leader transitions, bounded by MaxBecomeLeader
\* Candidate i transitions to leader. Candidate -> Leader
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats>>

\* Modified up to MaxTerm; Back To Follower
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm < MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars>>

\***************************** REQUEST VOTE **********************************************
\* Message handlers
\* i = recipient, j = sender, m = message

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\***************************** HovercRaft Additions  **********************************************
\* --- Step 1: Client sends request 'v' TO THE SWITCH ---
SwitchClientRequest(v) ==
    /\ maxc < MaxClientRequests \* Apply global request limit
    \* Update only the Switch's pending requests
    /\ pendingRequests' = [pendingRequests EXCEPT ![Switch] = @ \cup {v}]
    /\ maxc' = maxc + 1 \* Increment count when request enters the system
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars,
                   leaderCount, entryCommitStats, missingRequests>>
                   \* Note: pendingRequests for Server nodes are unchanged here.

\* --- Step 2: Switch disseminates a pending request 'v' TO ALL SERVERS ---
SwitchDisseminate(v) ==
    /\ v \in pendingRequests[Switch] \* Switch must have the request
    \* Update pendingRequests: Remove from Switch, add to all Servers
    /\ pendingRequests' = [ n \in Node |->
                              IF n = Switch THEN pendingRequests[n] \ {v}
                              ELSE IF n \in Server THEN pendingRequests[n] \cup {v}
                                   ELSE pendingRequests[n] \* Should not happen, but defensive
                          ]
    \* Note: maxc was already incremented by SwitchClientRequest
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars,
                   maxc, leaderCount, entryCommitStats, missingRequests>>

\* remove ClientMulticast(v) == ... (This action is now replaced by the two above)

\*\* --- HovercRaft Change: Client Interaction ---
\*\* Simulate the Switch multicasting a client request payload 'v' to all servers.
\*ClientMulticast(v) ==
\*    /\ maxc < MaxClientRequests \* Still apply global request limit
\*    /\ pendingRequests' = [i \in Server |-> pendingRequests[i] \cup {v}]
\*    /\ maxc' = maxc + 1 \* Increment count when request enters the system
\*    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars,
\*                   leaderCount, entryCommitStats, missingRequests>>


\* --- HovercRaft Change: Leader orders a request ---
\* Leader 'i' chooses a pending request 'v' to include in its log.
\* This replaces the original ClientRequest logic.
LeaderOrderRequest(i, v) ==
    /\ state[i] = Leader
    /\ v \in pendingRequests[i] \* Leader must have received the multicast
    /\ LET entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v] \* Entry contains metadata (term, value=request_id)
           \* Check if this exact value (request ID) is already *ordered* in the log
           alreadyOrdered == \E idx \in DOMAIN log[i] : log[i][idx].value = v
           newLog == IF alreadyOrdered THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == IF alreadyOrdered THEN 0 ELSE Len(log[i]) + 1 \* 0 if not new
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ pendingRequests' = [pendingRequests EXCEPT ![i] = pendingRequests[i] \ {v}] \* Remove from leader's pending
        /\ entryCommitStats' =
              IF /\ newEntryIndex > 0 \* Only add stats for newly ordered entries
                 /\ newEntryKey \notin DOMAIN entryCommitStats \* Avoid overwriting if somehow re-ordered
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
        /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex,
                       maxc, leaderCount, missingRequests>> \* maxc already incremented by ClientMulticast



\***************************** AppendEntries **********************************************

\* Original ClientRequest - Keep definition but EXCLUDE from Next state for HovercRaft run
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ maxc < MaxClientRequests
    /\ LET entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v]
           entryExists == \E j \in DOMAIN log[i] : log[i][j].value = v /\ log[i][j].term = entryTerm
           newLog == IF entryExists THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ maxc' = IF entryExists THEN maxc ELSE maxc + 1
        /\ entryCommitStats' =
              IF ~entryExists /\ newEntryIndex > 0 \* Only add stats for truly new entries
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount>>

\* Modified. Leader i sends j an AppendEntries request containing exactly 1 entry. It was up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
\* --- HovercRaft Change: AppendEntries sends metadata only ---
\* Leader i sends j an AppendEntries request containing exactly 1 *metadata* entry.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ Len(log[i]) > 0
    /\ nextIndex[i][j] <= Len(log[i])
    \* /\ matchIndex[i][j] < nextIndex[i][j] \* Original condition - can remove or keep, depends on retry logic desired. Let's keep it simple for now.
    /\ LET entryIndex == nextIndex[i][j]
           entryMetadata == log[i][entryIndex] \* This is [term |-> t, value |-> v]
           entries == << entryMetadata >> \* Send only the metadata entry
           entryKey == <<entryIndex, entryMetadata.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,       \* Metadata only
                mlog           |-> log[i],        \* Keep for history variable/proofs if needed
                mcommitIndex   |-> Min({commitIndex[i], entryIndex -1 }), \* Commit up to previous entry
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount,
                   pendingRequests, missingRequests>> \* pendingRequests is UNCHANGED here


\* --- HovercRaft Actions: Recovery Mechanism (Helper Action) ---
\* Note: This is defined separately for clarity but used within HandleAppendEntriesRequest
\* Follower i sends a RecoveryRequest for payload v to leader j
SendRecoveryRequest(i, j, v) ==
    /\ Send([mtype         |-> RecoveryRequest,
             mterm         |-> currentTerm[i],
             mRequestValue |-> v,
             msource       |-> i,
             mdest         |-> j])
    \* This action only modifies 'messages'. Other UNCHANGED are handled by the caller.


\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
\* --- HovercRaft Change: HandleAppendEntriesRequest checks pendingRequests ---
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
        acceptRequestLogic(newState) ==
            /\ m.mterm = currentTerm[i]
            /\ newState = Follower \* Must be follower to accept
            /\ logOk
            /\ LET index == m.mprevLogIndex + 1
               IN \/ \* Heartbeat or already have this exact entry
                     /\ \/ m.mentries = << >>
                        \/ /\ Len(log[i]) >= index
                           /\ log[i][index] = m.mentries[1] \* Compare full metadata entry
                     /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                     /\ Reply([mtype           |-> AppendEntriesResponse,
                               mterm           |-> currentTerm[i],
                               msuccess        |-> TRUE,
                               mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                               msource         |-> i,
                               mdest           |-> j], m)
                     /\ UNCHANGED <<serverVars, log, pendingRequests, missingRequests>> \* pendingRequests is UNCHANGED here
                  \/ \* Conflict: remove entries (same logic as before)
                     /\ m.mentries /= << >>
                     /\ Len(log[i]) >= index
                     /\ log[i][index].term /= m.mentries[1].term
                     /\ LET newLog == SubSeq(log[i], 1, index - 1)
                        IN log' = [log EXCEPT ![i] = newLog]
                     \* Reply implicitly handled by leader retry on failure (no Reply action here)
                     /\ UNCHANGED <<serverVars, commitIndex, messages, pendingRequests, missingRequests>> \* pendingRequests is UNCHANGED here
                  \/ \* Append new entry: Check for payload before appending
                     /\ m.mentries /= << >>
                     /\ Len(log[i]) = m.mprevLogIndex
                     /\ LET entryMetadata == m.mentries[1]
                           payloadValue == entryMetadata.value
                        IN \/ \* Payload IS available
                              /\ payloadValue \in pendingRequests[i] \* Condition
                              /\ log' = [log EXCEPT ![i] = Append(log[i], entryMetadata)] \* Update
                              /\ pendingRequests' = [pendingRequests EXCEPT ![i] = pendingRequests[i] \ {payloadValue}] \* Update
                              /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex] \* Update
                              /\ Reply([mtype           |-> AppendEntriesResponse, \* Update (messages')
                                        mterm           |-> currentTerm[i],
                                        msuccess        |-> TRUE,
                                        mmatchIndex     |-> index,
                                        msource         |-> i,
                                        mdest           |-> j], m)
                              /\ UNCHANGED <<serverVars, missingRequests>> \* Update (others)

                           \/ \* Payload is MISSING
                              /\ payloadValue \notin pendingRequests[i] \* Condition
                              /\ Reply([mtype           |-> AppendEntriesResponse, \* Update (messages') - Always reply FALSE if missing
                                        mterm           |-> currentTerm[i],
                                        msuccess        |-> FALSE,
                                        mmatchIndex     |-> m.mprevLogIndex,
                                        msource         |-> i,
                                        mdest           |-> j], m)
                              /\ IF payloadValue \notin missingRequests[i] \* Condition for *specific* updates when missing
                                 THEN /\ SendRecoveryRequest(i, j, payloadValue) \* Update (messages' again)
                                      /\ missingRequests' = [missingRequests EXCEPT ![i] = missingRequests[i] \cup {payloadValue}] \* Update (missingRequests')
                                 ELSE /\ UNCHANGED <<messages, missingRequests>> \* Update (no change to these if already requested)
                              /\ UNCHANGED <<serverVars, log, commitIndex, pendingRequests>> \* pendingRequests is UNCHANGED here

    IN /\ m.mterm <= currentTerm[i]  \* Overall precondition
       /\ ( \* Start of main disjunction for handling paths
             \/ /\ \* Path 1: Reject request
                   ( \/ m.mterm < currentTerm[i]  \* Guard condition 1 for rejection
                     \/ /\ m.mterm = currentTerm[i] \* Guard condition 2 for rejection
                        /\ state[i] = Follower
                        /\ \lnot logOk
                   ) \* End of rejection guard condition
                   /\ Reply([mtype           |-> AppendEntriesResponse, \* Action if rejected
                             mterm           |-> currentTerm[i],
                             msuccess        |-> FALSE,
                             mmatchIndex     |-> 0,
                             msource         |-> i,
                             mdest           |-> j], m)
                   /\ UNCHANGED <<serverVars, logVars, pendingRequests, missingRequests>> \* State if rejected and pendingRequests is UNCHANGED here

             \/ /\ \* Path 2: Step down if candidate
                   m.mterm = currentTerm[i]
                   /\ state[i] = Candidate
                   /\ state' = [state EXCEPT ![i] = Follower] \* Action if stepping down
                   /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, pendingRequests, missingRequests>> \* State if stepping down and pendingRequests is UNCHANGED here

             \/ /\ \* Path 3: Accept request (or trigger recovery)
                   acceptRequestLogic(state[i]) \* This LET definition contains the complex logic for accepting/recovering
                   /\ UNCHANGED <<candidateVars, leaderVars>> \* acceptRequestLogic handles relevant state changes, these vars not involved

          ) \* End of main disjunction
       /\ UNCHANGED <<instrumentationVars>> \* entryCommitStats unchanged on followers generally


\* Leader i handles RecoveryRequest for value v from follower j
\* Leader checks its *log* to see if it has ordered this value.
\* Simplification: Assume leader has the payload if it's in its log.
HandleRecoveryRequest(i, j, m) ==
    LET requestedValue == m.mRequestValue
        \* Check if the leader has ordered this value (i.e., it's in the log)
        hasValue == \E idx \in DOMAIN log[i] : log[i][idx].value = requestedValue
    IN /\ m.mterm <= currentTerm[i] \* Ignore stale requests, respond with current term if lower
       /\ IF hasValue
          THEN Reply([mtype         |-> RecoveryResponse,
                      mterm         |-> currentTerm[i],
                      mRequestValue |-> requestedValue,
                      \* No separate payload field needed if Value is the payload
                      msource       |-> i,
                      mdest         |-> j], m)
          ELSE Discard(m) \* Leader doesn't have it (maybe lost leadership?), ignore.
       /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars,
                      pendingRequests, missingRequests>> \* pendingRequests is UNCHANGED here

\* Follower i handles RecoveryResponse for value v from leader j
HandleRecoveryResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i] \* Precondition
    /\ ( LET recoveredValue == m.mRequestValue \* Group the LET...IN block
         IN /\ pendingRequests' = [pendingRequests EXCEPT ![i] = pendingRequests[i] \cup {recoveredValue}]
            /\ missingRequests' = [missingRequests EXCEPT ![i] = missingRequests[i] \ {recoveredValue}]
            /\ Discard(m)
       ) \* End group
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>> \* pendingRequests is UNCHANGED here


\* HandleAppendEntriesResponse: No changes needed for HovercRaft core logic.
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Leader \* Only leaders process these responses
    /\ \/ /\ m.msuccess \* successful
          /\ LET newMatchIndex == m.mmatchIndex
                 \* Find the corresponding entry key using the acknowledged index
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>> \* Invalid index or empty log
             IN /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = newMatchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = newMatchIndex]
                /\ entryCommitStats' =
                     IF /\ entryKey /= <<0, 0>>
                        /\ entryKey \in DOMAIN entryCommitStats
                        /\ ~entryCommitStats[entryKey].committed
                     THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                     ELSE entryCommitStats
       \/ /\ \lnot m.msuccess \* not successful
          \* If follower rejected due to missing payload, leader will eventually retry AppendEntries
          \* for that index after nextIndex[i][j] is potentially decremented here.
          \* If follower rejected due to log mismatch (m.mterm > currentTerm[j] response implicit),
          \* leader might decrement nextIndex based on that future response or current logic.
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, entryCommitStats>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxc, leaderCount,
                   pendingRequests, missingRequests>> \* pendingRequests is UNCHANGED here

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           committedIndexes == { k \in Nat : /\ k > commitIndex[i]
                                             /\ k <= newCommitIndex }
           \* Identify the keys in entryCommitStats corresponding to newly committed entries
           keysToUpdate == { key \in DOMAIN entryCommitStats : key[1] \in committedIndexes }
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          \* Update the 'committed' flag for the relevant entries in entryCommitStats
          /\ entryCommitStats' =
               [ key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ] \* Update record
                   ELSE entryCommitStats[key] ]                             \* Keep old record
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount, pendingRequests, missingRequests>>
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, pendingRequests, missingRequests>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, pendingRequests, missingRequests>>

=============================================================================
\* Created by Ovidiu-Cristian Marcu
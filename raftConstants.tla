--------------------------- MODULE raftConstants ---------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* A dedicated identifier for the Switch component
CONSTANTS Switch

\* The set of all nodes in the system (Raft Servers + Switch)
Node == Server \union {Switch}

\* The set of client requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse,
          \* --- HovercRaft Additions ---
          RecoveryRequest, RecoveryResponse
          
\* for instrumentation to limit model state space
CONSTANTS MaxClientRequests 

\* Maximum times a server can become a leader
CONSTANTS MaxBecomeLeader

\* Maximum term number allowed in the model
CONSTANTS MaxTerm

=============================================================================
\* Created by Ovidiu-Cristian Marcu
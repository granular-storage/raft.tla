--------------------------- MODULE raftConstants ---------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of client requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

\* for instrumentation to limit model state space
CONSTANTS MaxClientRequests

\* Maximum times a server can become a leader
CONSTANTS MaxBecomeLeader

\* Maximum term number allowed in the model
CONSTANTS MaxTerm

CONSTANTS SwitchPayload \*SwitchPayload � for the full client request payload delivered via multicast.
CONSTANTS RecoveryRequest \*RecoveryRequest (and optionally RecoveryResponse) � to support the bonus recovery mechanism.
CONSTANTS RecoveryResponse
=============================================================================
\* Created by Ovidiu-Cristian Marcu

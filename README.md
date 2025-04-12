
Formal TLA+ specification for the [Raft consensus algorithm](https://raftconsensus.github.io). This is slightly updated compared to the dissertation version.

For more information, see Chapter 8 (Correctness) and Appendix B (Safety proof and formal specification) in https://github.com/ongardie/dissertation .

If you're trying to run the TLA+ model checker on this specification, check out Jin Li's changes in [Pull Request #4](https://github.com/ongardie/raft.tla/pull/4/).

Copyright 2014 Diego Ongaro.

This work is licensed under the Creative Commons Attribution-4.0 International License https://creativecommons.org/licenses/by/4.0/ .

Modified by Ovidiu Marcu

How to run?

The following runs with Restart, DuplicateMessage, DropMessage and leader actions disabled.

1)
You can run one configuration see raft.cfg with: ./tlc.py --coverage 1 mc raftModelPerf.tla, at branch raftEntryCommits commit.

This state from a 14 steps invalidates LeaderCommited fake invariant with entryCommitStats updated.

State 14: <MyNext line 54, col 15 to line 55, col 93 of module raftSpec>
/\ messages = ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 2] :> 1 @@ [mdest |-> r1, msource |-> r3, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 1 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 1, mprevLogTerm |-> 2, mentries |-> <<[term |-> 2, value |-> v1]>>, mcommitIndex |-> 1] :> 0 @@ [mdest |-> r3, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 1] :> 0)
/\ matchIndex = ( r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) )
/\ log = ( r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@
  r2 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@
  r3 :> <<[term |-> 2, value |-> v2]>> )
/\ state = (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower)
/\ leaderCount = (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0)
/\ entryCommitStats = ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] )
/\ commitIndex = (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)
/\ currentTerm = (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2)
/\ votesResponded = (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
/\ maxc = 2
/\ nextIndex = ( r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) )
/\ votesGranted = (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
/\ voterLog = (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>)
/\ votedFor = (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1)

59592 states generated, 21204 distinct states found, 9855 states left on queue.
The depth of the complete state graph search is 18.
Finished in 03s at (2025-03-31 13:39:43)
My configuration:
Running breadth-first search Model-Checking with 32 workers on 32 cores with 7282MB heap and 4096MB offheap memory [pid: 1231] (Linux 5.15.167.4-microsoft-standard-WSL2 amd64, Ubuntu 11.0.26 x86_64, MSBDiskFPSet, DiskStateQueue).

OR 

2)
model check the following with the Toolbox:

State constraint for model checking

MyConstraint

Disable Profiling in TLC Options. See screenshots, raftModelPerf.cfg for initializing model and expected results.

TLC command line parameters: -coverage 1

For MySpec we obtain this trace that invalidates LeaderCommitted fake invariant.

With this Init
/\  commitIndex = [r1 |-> 1, r2 |-> 1, r3 |-> 1]
/\  currentTerm = [r1 |-> 2, r2 |-> 2, r3 |-> 2]
/\  entryCommitStats = ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] )
/\  leaderCount = [r1 |-> 1, r2 |-> 0, r3 |-> 0]
/\  log = [ r1 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ]
/\  matchIndex = [ r1 |-> [r1 |-> 0, r2 |-> 1, r3 |-> 0],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ]
/\  maxc = 2
/\  messages = ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 )
/\  nextIndex = [ r1 |-> [r1 |-> 1, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ]
/\  state = [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower]
/\  votedFor = [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"]
/\  voterLog = [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>]
/\  votesGranted = [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
/\  votesResponded = [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]

and MyNext

and

\* fake inv to obtain a trace
LeaderCommitted ==
    \E i \in Server : commitIndex[i] /= 2 \*


<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
 commitIndex |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 1, r3 |-> 0],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 2,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "MyNext",
   location |-> "line 51, col 46 to line 51, col 85 of module raftSpec"
 ],
 commitIndex |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 1, r3 |-> 0],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 3,
   name |-> "MyNext",
   location |-> "line 54, col 15 to line 55, col 93 of module raftSpec"
 ],
 commitIndex |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 1] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 2, r3 |-> 0],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 3, r3 |-> 1],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 4,
   name |-> "AdvanceCommitIndex",
   location |-> "line 293, col 5 to line 319, col 92 of module raftActionsSolution"
 ],
 commitIndex |-> [r1 |-> 2, r2 |-> 1, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 2, r3 |-> 0],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 3, r3 |-> 1],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 5,
   name |-> "MyNext",
   location |-> "line 53, col 35 to line 53, col 63 of module raftSpec"
 ],
 commitIndex |-> [r1 |-> 2, r2 |-> 1, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 2, r3 |-> 0],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 2,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v4"]>>,
    mcommitIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 3, r3 |-> 1],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 6,
   name |-> "MyNext",
   location |-> "line 54, col 15 to line 55, col 93 of module raftSpec"
 ],
 commitIndex |-> [r1 |-> 2, r2 |-> 1, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 2,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v4"]>>,
    mcommitIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 3, r3 |-> 2],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 7,
   name |-> "MyNext",
   location |-> "line 53, col 35 to line 53, col 63 of module raftSpec"
 ],
 commitIndex |-> [r1 |-> 2, r2 |-> 1, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 2,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v4"]>>,
    mcommitIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 2 ] :>
      1 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 3, r3 |-> 2],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 8,
   name |-> "MyNext",
   location |-> "line 54, col 15 to line 55, col 93 of module raftSpec"
 ],
 commitIndex |-> [r1 |-> 2, r2 |-> 1, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 2,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v4"]>>,
    mcommitIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 2 ] :>
      1 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 3, r3 |-> 2],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 9,
   name |-> "MyNext",
   location |-> "line 54, col 15 to line 55, col 93 of module raftSpec"
 ],
 commitIndex |-> [r1 |-> 2, r2 |-> 1, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r3 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 2,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v4"]>>,
    mcommitIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 2 ] :>
      1 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 3, r3 |-> 2],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 10,
   name |-> "MyNext",
   location |-> "line 54, col 15 to line 55, col 93 of module raftSpec"
 ],
 commitIndex |-> [r1 |-> 2, r2 |-> 2, r3 |-> 1],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r3 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 3 ] :>
      1 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 2,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v4"]>>,
    mcommitIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 2 ] :>
      1 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 3, r3 |-> 2],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
],
[
 _TEAction |-> [
   position |-> 11,
   name |-> "MyNext",
   location |-> "line 54, col 15 to line 55, col 93 of module raftSpec"
 ],
 commitIndex |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 currentTerm |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2],
 entryCommitStats |-> ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<3, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] ),
 leaderCount |-> [r1 |-> 1, r2 |-> 0, r3 |-> 0],
 log |-> [ r1 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r2 |->
      << [term |-> 2, value |-> "v1"],
         [term |-> 2, value |-> "v2"],
         [term |-> 2, value |-> "v4"] >>,
  r3 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>> ],
 matchIndex |-> [ r1 |-> [r1 |-> 0, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ],
 maxc |-> 3,
 messages |-> ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 3 ] :>
      1 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 2,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v4"]>>,
    mcommitIndex |-> 2 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |->
        << [term |-> 2, value |-> "v1"],
           [term |-> 2, value |-> "v2"],
           [term |-> 2, value |-> "v4"] >>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 2 ] :>
      0 ),
 nextIndex |-> [ r1 |-> [r1 |-> 1, r2 |-> 3, r3 |-> 2],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ],
 state |-> [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower],
 votedFor |-> [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"],
 voterLog |-> [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>],
 votesGranted |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}],
 votesResponded |-> [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
]
>>

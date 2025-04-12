---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174449477938292000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_174449477938293000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_174449477938294000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_174449477938295000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_174449477938296000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174449477938297000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sat Apr 12 23:52:59 CEST 2025 by parsa

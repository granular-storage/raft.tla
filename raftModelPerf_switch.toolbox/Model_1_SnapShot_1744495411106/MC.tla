---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_1744495406965122000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_1744495406965123000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_1744495406965124000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_1744495406965125000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_1744495406965126000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1744495406965127000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sun Apr 13 00:03:26 CEST 2025 by parsa

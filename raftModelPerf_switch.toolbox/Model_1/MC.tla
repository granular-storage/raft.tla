---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_1744022005823289000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_1744022005823290000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_1744022005823291000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_1744022005823292000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_1744022005823293000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1744022005823294000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Mon Apr 07 12:33:25 CEST 2025 by parsa

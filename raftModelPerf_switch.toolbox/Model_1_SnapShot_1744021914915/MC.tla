---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_1744021900789169000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_1744021900789170000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_1744021900789171000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_1744021900789172000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_1744021900789173000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1744021900789174000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Mon Apr 07 12:31:40 CEST 2025 by parsa

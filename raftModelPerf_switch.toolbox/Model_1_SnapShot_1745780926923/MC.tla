---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_1745780563395285000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_1745780563395286000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_1745780563395287000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_1745780563395288000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_1745780563395289000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:15Switch
const_1745780563395290000 == 
"sw"
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1745780563395291000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sun Apr 27 21:02:43 CEST 2025 by parsa

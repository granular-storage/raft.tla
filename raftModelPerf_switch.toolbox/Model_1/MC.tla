---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_1745781417190333000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_1745781417190334000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_1745781417190335000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_1745781417190336000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_1745781417190337000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:15Switch
const_1745781417190338000 == 
"sw"
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1745781417190339000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sun Apr 27 21:16:57 CEST 2025 by parsa

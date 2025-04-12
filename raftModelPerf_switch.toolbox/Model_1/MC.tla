---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_17444516180432000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_17444516180433000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_17444516180434000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_17444516180435000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_17444516180436000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_17444516180437000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sat Apr 12 11:53:38 CEST 2025 by parsa

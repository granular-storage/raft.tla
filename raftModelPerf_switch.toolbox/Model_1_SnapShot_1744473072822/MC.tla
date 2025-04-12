---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174447306864675000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_174447306864676000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_174447306864677000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_174447306864678000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_174447306864679000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174447306864680000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sat Apr 12 17:51:08 CEST 2025 by parsa

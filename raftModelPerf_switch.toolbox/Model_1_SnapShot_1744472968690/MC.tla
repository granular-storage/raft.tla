---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174447296419532000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_174447296419533000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_174447296419534000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_174447296419535000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_174447296419536000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174447296419537000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sat Apr 12 17:49:24 CEST 2025 by parsa

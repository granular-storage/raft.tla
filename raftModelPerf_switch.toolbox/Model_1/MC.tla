---- MODULE MC ----
EXTENDS raftModelPerf, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174703746915119000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_174703746915120000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:10Value
const_174703746915121000 == 
{"v1","v2"}
----

\* CONSTANT definitions @modelParameterConstants:11Server
const_174703746915122000 == 
{"r1","r2","r3"}
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_174703746915123000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:15Switch
const_174703746915124000 == 
"sw"
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174703746915125000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Mon May 12 10:11:09 CEST 2025 by parsa

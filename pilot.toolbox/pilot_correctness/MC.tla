---- MODULE MC ----
EXTENDS pilot, TLC

\* CONSTANT definitions @modelParameterConstants:0Policies
const_17125607731789000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:1DSs
const_171256077317810000 == 
{"ds1"}
----

\* CONSTANT definitions @modelParameterConstants:2DCs
const_171256077317811000 == 
{"dc1", "dc2"}
----

\* CONSTANT definitions @modelParameterConstants:3poPolicies
const_171256077317812000 == 
{ << p, p >> : p \in Policies } \cup {<<"p1","p2">>}
----

\* CONSTANT definitions @modelParameterConstants:4Devices
const_171256077317813000 == 
DSs \cup DCs
----

=============================================================================
\* Modification History
\* Created Mon Apr 08 09:19:33 CEST 2024 by pardo

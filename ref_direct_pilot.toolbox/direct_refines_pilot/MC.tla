---- MODULE MC ----
EXTENDS ref_direct_pilot, TLC

\* CONSTANT definitions @modelParameterConstants:0Policies
const_171256078239516000 == 
{"p1","p2","p3"}
----

\* CONSTANT definitions @modelParameterConstants:1DSs
const_171256078239517000 == 
{"ds1"}
----

\* CONSTANT definitions @modelParameterConstants:2DCs
const_171256078239518000 == 
{"dc1","dc2"}
----

\* CONSTANT definitions @modelParameterConstants:3poPolicies
const_171256078239519000 == 
{<<p,p>> : p \in Policies} \cup {<<"p1","p2">>}
----

\* CONSTANT definitions @modelParameterConstants:4Devices
const_171256078239520000 == 
DSs \cup DCs
----

=============================================================================
\* Modification History
\* Created Mon Apr 08 09:19:42 CEST 2024 by pardo

---- MODULE MC ----
EXTENDS ref_indirect_pilot, TLC

\* CONSTANT definitions @modelParameterConstants:0Policies
const_1711905987010208000 == 
{"p1","p2","p3"}
----

\* CONSTANT definitions @modelParameterConstants:1DSs
const_1711905987010209000 == 
{"ds1"}
----

\* CONSTANT definitions @modelParameterConstants:2DCs
const_1711905987010210000 == 
{"dc1","dc2"}
----

\* CONSTANT definitions @modelParameterConstants:3poPolicies
const_1711905987010211000 == 
{<<p,p>> : p \in Policies} \cup {<<"p1","p2">>}
----

\* CONSTANT definitions @modelParameterConstants:4Devices
const_1711905987010212000 == 
DSs \cup DCs
----

=============================================================================
\* Modification History
\* Created Sun Mar 31 19:26:27 CEST 2024 by pardo

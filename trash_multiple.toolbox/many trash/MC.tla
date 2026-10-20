---- MODULE MC ----
EXTENDS trash_multiple, TLC

\* CONSTANT definitions @modelParameterConstants:0NumUsers
const_17914529725462000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1NumTrucks
const_17914529725463000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2MaxCapacity
const_17914529725464000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3MaxUserTrash
const_17914529725465000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4NumBins
const_17914529725466000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_17914529725467000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_17914529725478000 ==
OuterDoorLocked
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_17914529725479000 ==
RamOuterDoor
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_179145297254710000 ==
TrashEmptied
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_179145297254711000 ==
AuthorizedOpenOnly
----
=============================================================================
\* Modification History
\* Created Thu Oct 08 11:49:32 CEST 2026 by jerzy

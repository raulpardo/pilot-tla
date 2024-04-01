# TLA+ Mechanization of PILOT semantics and refinements

This repository accompanies the paper "Model-Checking the Implementation of Consent". The repository contains the TLA+ specification of the abstract semantics of privacy policy language PILOT and two refinements.

The content of the repository is:

* `pilot.tla` - TLA+ spec of PILOT abstract semantics. It also contains the formalization of the 3 properties for consent described in the paper
* `ref_direct_pilot.tla` - TLA+ spec of the program graph using an architecture where devices communicate directly to each other. It contains the property stating that this program graph refines pilot semantics. 
* `ref_indirect_pilot.tla` - TLA+ spec of the program graph using an architecture where devices cannot communicate directly, and use a public privacy policy repository to exchange policies. It contains the property stating that this program graph refines pilot semantics.


## Verification

We provide models to run model-checking on the specification and properties above. 

* For verifying the consent properties on PILOT semantics, start the TLA+ toolbox, select File -> Open Spec -> Add New Spec... and then select the `pilot.tla` file. On the left panel, you will see a model called `pilot_correctness`. You can click on it and press play to run the model-checking algorithm on the properties mentioned above.

* For verifying that the direct and indirect program graphs refine pilot semantics. Open (as mentioned above) the spec of `ref_direct_pilot.tla` or `ref_indirect_pilot.tla`. On the left panel you will see the models `direct_refines_pilot` or `indirect_refines_pilot`, respectively. Click on the corresponding model and click play to run the model-checking algorithm that verifies that these two implementations refine PILOT abstract semantics.

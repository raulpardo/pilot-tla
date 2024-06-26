---------------------------- MODULE pilot ----------------------------

(***************************************************************************)
(* This module is a mechanized version of the semantics of the privacy     *)
(* policy language PILOT.  See accompanying paper.                         *)
(*                                                                         *)
(* The mapping of the theoretical definition of the semantics and the      *)
(* definitions here is almost direct.  This is because all the operations  *)
(* to define the semantics are available in TLA+.  Nevertheless, this      *)
(* semantics makes a few simplifications compared to the definitions in    *)
(* the paper: i) the state operates on a single data item.  This is        *)
(* because the PILOT language handles the communication and processing of  *)
(* each item independently.  ii) The structure of PILOT policies has been  *)
(* abstracted away.  The reason for this is minimize the amount of memory  *)
(* required for model checking.  Note that in the PILOT semantics the key  *)
(* constraint to determine whether data may be transferred is the partial  *)
(* order between policies.  That is, whether the receiver has more         *)
(* restrictive policy than the sender.  In this mechanization, policies    *)
(* are strings and we model explicitly the partial order between policies. *)
(* A more elaborate mechanization should include all the elements of PILOT *)
(* policies and implement the partial order relation as defined in the     *)
(* paper.  This change also has the impact on data transfers.  They are    *)
(* allowed if the senders policy is more restrictive than that of          *)
(* receiver.  This is sound as the subsumption definition requires the set *)
(* of transfers to be more constraint for the receiver policy.  iii) The   *)
(* request event always updates the policy in the receiving device (as     *)
(* opposed to how R2 is defined in the paper where there is a check that   *)
(* the new policy must be more restrictive).  Since we are operating on a  *)
(* single item, this modification is sound.  At the moment, the semantics  *)
(* of PILOT do not support changing the policy associated to a data item   *)
(* that has already been collected.  This is a tricky issue from the legal *)
(* point of view, and we postpone handling those details as future work.   *)
(*                                                                         *)
(***************************************************************************)


EXTENDS Integers, FiniteSets

CONSTANT
    DSs,
    DCs,
    Policies,
    poPolicies,
    Devices

ASSUME
    \* poPolicies is a set of pairs of policies
    /\ poPolicies \subseteq { << p1, p2 >> : p1,p2 \in Policies}
    \* poPolicies is a partial order    
    /\ \A p \in Policies : 
            << p, p >> \in poPolicies
    /\ \A p1,p2,p3 \in Policies : 
            << p1, p2 >> \in poPolicies /\ << p2, p3 >> \in poPolicies 
            => 
            << p1, p3 >> \in poPolicies
    /\ \A p1,p2 \in Policies :
            << p1, p2 >> \in poPolicies /\ << p2, p1 >> \in poPolicies
            =>
            p1 = p2
    /\ Devices \subseteq DSs \cup DCs
    /\ Cardinality(DSs) = 1 \* Otherwise we need to change received_data (we assume one data item)
    

-----------------------------------------------------------------------------

VARIABLES 
    received_data, \* Indicates communicating of data together with the applicable policy
                    (********************************************************)
                    (* received_data(d1)(d2) = p is read as ``device d1 has *)
                    (* sent data to device d2 and p is the policy that      *)
                    (* applies''                                            *)
                    (********************************************************)
    policy_base    \* Includes the policies in each device
                    (********************************************************)
                    (* policy_base(d1)(d2) = p is read as ``device d1 has   *)
                    (* received policy p from d2''.  We use the case d1 =   *)
                    (* d2 to represent policies that have been input in the *)
                    (* device by the DS or DC herself.                      *)
                    (********************************************************)  

vars == << policy_base, received_data >>

TypeOK == /\ policy_base \in [ Devices -> [ Devices -> Policies \cup {"0"} ] ] \* Ensures one policy per pair of devices
          /\ received_data \in [ Devices -> [ DCs -> Policies \cup {"0"} ] ]
          /\ \A dc \in DCs : received_data[dc][dc] = "0"

-----------------------------------------------------------------------------

Init == /\ policy_base   = [ d1 \in Devices |-> [ d2 \in Devices |-> "0" ] ]
        /\ received_data = [ d \in Devices |-> [ dc \in DCs |-> "0" ] ]
        
-----------------------------------------------------------------------------

Choose_policy(d, p) == /\ policy_base[d][d] = "0"
                       /\ policy_base' = [ policy_base EXCEPT ![d][d] = p]                           
                       /\ UNCHANGED << received_data >>


Request_collection(sndr, rcv, p_dc) == /\ sndr # rcv
                                       /\ policy_base[sndr][sndr] # "0"
                                       /\ policy_base[sndr][sndr] = p_dc                                                                            
                                       /\ policy_base' = [ policy_base EXCEPT ![rcv][sndr] = p_dc ]                                       
                                       /\ UNCHANGED << received_data >>

Request_transfer(sndr, rcv, p_dc) == /\ sndr # rcv
                                     /\ policy_base[sndr][sndr] # "0"
                                     /\ policy_base[sndr][sndr] = p_dc                                                                              
                                     /\ policy_base' = [ policy_base EXCEPT ![rcv][sndr] = p_dc]
                                     /\ UNCHANGED << received_data >>


Send1(sndr, rcv, p_i) == /\ sndr # rcv
                         /\ policy_base[sndr][sndr] # "0"
                         /\ << policy_base[sndr][rcv], policy_base[sndr][sndr] >> \in poPolicies
                         /\ received_data' = [received_data EXCEPT ![sndr][rcv] = policy_base[sndr][rcv] ]
                         /\ UNCHANGED << policy_base >> 
                         


Transfer1(sndr, rcv, p_i) == /\ sndr # rcv
                             /\ policy_base[sndr][rcv] # "0"
                             /\ \E d \in Devices : 
                                    /\ received_data[d][sndr] # "0" 
                                    /\ << policy_base[sndr][rcv], received_data[d][sndr] >> \in poPolicies
                             /\ policy_base[sndr][rcv] = p_i
                             /\ received_data' = [received_data EXCEPT ![sndr][rcv] = policy_base[sndr][rcv] ]                             
                             /\ UNCHANGED << policy_base >>



Next == \E dc1,dc2 \in DCs : 
            \E p \in Policies :
                \E ds \in DSs : 
                    \/ Choose_policy(dc1,p)
                    \/ Choose_policy(ds,p)
                    \/ Request_collection(dc1,ds,p)
                    \/ Request_transfer(dc1,dc2,p)
                    \/ Send1(ds,dc1,p)
                    \/ Transfer1(dc1,dc2,p)

-----------------------------------------------------------------------------

SimplePilotSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
             
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

(***************************************************************************)
(* The policy of the DS is always more restrictive than the policies that  *)
(* the DCs that have collected the data apply.                             *)
(***************************************************************************)  
AlwaysSatisfyDSPolicy == \A d \in Devices, dc \in DCs, ds \in DSs : 
                            received_data[d][dc] # "0" 
                            => 
                            << received_data[d][dc], policy_base[ds][ds] >> \in poPolicies  

(***************************************************************************)
(* We say that a DS is ``informed'' if before sending the data it has      *)
(* received the policy of the receiver.  The following formula expresses   *)
(* this property when data is sent (i.e., collected by a DC).              *)
(*                                                                         *)
(*                                                                         *)
(* Interestingly, this property also guarantees that the only way for a DC *)
(* to impersonate another, is by inputting a policy of the ``victim DC''   *)
(* in its policy_base.  Therefore, in order to avoid ``impersonation       *)
(* attacks'' we simply need to assume that for all policies in             *)
(* policy_base(d)(d) the owner of the policy is device d.                  *)
(***************************************************************************)

InformedDS == \A dc \in DCs, ds \in DSs : 
                received_data[ds][dc] # "0" 
                => 
                policy_base[ds][dc] = policy_base[dc][dc]
                
=============================================================================
\* Modification History
\* Last modified Wed Jun 26 17:32:28 CEST 2024 by pardo

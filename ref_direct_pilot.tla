------------------------- MODULE ref_direct_pilot -------------------------
(***************************************************************************)
(* This module is a mechanized version of the refinement for direct        *)
(* communication in the accompanying paper.                                *)
(***************************************************************************)


EXTENDS Integers, FiniteSets

CONSTANT
    DSs,
    DCs,
    Policies,
    Devices,
    poPolicies

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
    /\ Cardinality(DSs) = 1 \* Otherwise we need to change received_data

Messages ==
    [ type: {"policy"}, sender: Devices, recepient: Devices, policy: Policies ]
    \cup
    [ type: {"data"}, sender: Devices, recepient: DCs, policy: Policies ]

-----------------------------------------------------------------------------

VARIABLES    
    DS_state,      \* Current state of the DS machine    
    DC_state,      \* Current state of the DC machine   
    received_data, \* Indicates communicating of data together with the applicable policy
                    (********************************************************)
                    (* received_data(d1)(d2) = p is read as ``device d1 has *)
                    (* sent data to device d2 and p is the policy that      *)
                    (* applies''                                            *)
                    (********************************************************)
    policy_base,   \* Includes the policies in each device
                    (********************************************************)
                    (* policy_base(d1)(d2) = p is read as ``device d1 has   *)
                    (* received policy p from d2''.  We use the case d1 =   *)
                    (* d2 to represent policies that have been input in the *)
                    (* device by the DS or DC herself.                      *)
                    (********************************************************)  
    msgs
        (*******************************************************************)
        (* It models messages in transit.  A device can send a message,    *)
        (* i.e., put a message in the msgs set, or read a message, i.e.,   *)
        (* take a message out of the set.                                  *)
        (*******************************************************************)

Refvars == << DS_state, DC_state, policy_base, received_data, msgs >>


RefTypeOK == /\ DS_state  \in {"s0", "s1", "s2"}                               
             /\ DC_state  \in [ DCs -> {"s0", "s1", "s2", "s3", "s4"} ]
             /\ policy_base \in [ Devices -> [ Devices -> Policies \cup {"0"} ] ] \* Ensures one policy per pair of devices
             /\ received_data \in [ Devices -> [ DCs -> Policies \cup {"0"} ] ]
             /\ \A dc \in DCs : received_data[dc][dc] = "0"
             /\ msgs \subseteq Messages

-----------------------------------------------------------------------------

RefInit == /\ DS_state      = "s0"         
           /\ DC_state      = [ dc \in DCs |-> "s0" ]
           /\ policy_base   = [ d1 \in Devices |-> [ d2 \in Devices |-> "0" ] ]
           /\ received_data = [ d \in Devices |-> [ dc \in DCs |-> "0" ] ]
           /\ msgs          = {}
        
-----------------------------------------------------------------------------
        
(***************************************************************************)
(* DS device events                                                        *)
(***************************************************************************)

RefChoose_DS_policy(ds, p) == /\ DS_state = "s0"
                              /\ policy_base' = [ policy_base EXCEPT ![ds][ds] = p]
                              /\ DS_state' = "s1"
                              /\ UNCHANGED << DC_state, received_data, msgs >>

RefRequest_receive_DS(sndr, rcv, p_dc) == /\ DS_state  = "s1"
                                          /\ \E m \in msgs :
                                                  /\ m.type = "policy"
                                                  /\ m.sender = sndr
                                                  /\ m.recepient = rcv
                                                  /\ m.policy = p_dc
                                                  /\ policy_base' = [ policy_base EXCEPT ![rcv][m.sender] = m.policy ]
                                                  /\ msgs' = msgs \ {m}                                        
                                          /\ DS_state' = "s2"
                                          /\ UNCHANGED << DC_state, received_data >>

RefSend1_send_DS(sndr, rcv, p_i) == /\ DS_state = "s2"
                                    /\ policy_base[sndr][rcv] # "0"
                                    /\ << policy_base[sndr][rcv], policy_base[sndr][sndr] >> \in poPolicies
                                    /\ policy_base[sndr][rcv] = p_i
                                    /\ msgs' = msgs \cup { [ type      |-> "data", 
                                                             sender    |-> sndr, 
                                                             recepient |-> rcv,
                                                             policy    |-> policy_base[sndr][rcv] ] }
                                    /\ DS_state' = "s1"
                                    /\ UNCHANGED << DC_state, policy_base, received_data >>

RefSend2_send_DS(sndr, rcv) == /\ DS_state = "s2"
                               /\ policy_base[sndr][rcv] # "0"
                               /\ << policy_base[sndr][rcv], policy_base[sndr][sndr] >> \notin poPolicies                                 
                               /\ DS_state' = "s1"
                               /\ UNCHANGED << DC_state, policy_base, received_data, msgs >>
                                                    
-----------------------------------------------------------------------------

(***************************************************************************)
(* DC device events                                                        *)
(***************************************************************************)

RefChoose_DC_policy(dc, p) == /\ DC_state[dc] = "s0"
                              /\ policy_base' = [ policy_base EXCEPT ![dc][dc] = p]
                              /\ DC_state' = [ DC_state EXCEPT ![dc] = "s1" ]
                              /\ UNCHANGED << DS_state, received_data, msgs >>


RefRequest1_send_DC(sndr, rcv, p_dc) == /\ DC_state[sndr] = "s1"
                                        /\ policy_base[sndr][sndr] = p_dc                                    
                                        /\ msgs' = msgs \cup { [ type      |-> "policy", 
                                                                 sender    |-> sndr, 
                                                                 recepient |-> rcv,
                                                                 policy    |-> policy_base[sndr][sndr] ] }
                                        /\ DC_state' = [ DC_state EXCEPT ![sndr] = "s2" ]
                                        /\ UNCHANGED << DS_state, policy_base, received_data >>

RefRequest2_receive_DC(sndr, rcv, p_dc) == /\ DC_state[rcv]  = "s3"
                                           /\ \E m \in msgs :
                                                   /\ m.type = "policy"
                                                   /\ m.sender = sndr
                                                   /\ m.recepient = rcv
                                                   /\ m.policy = p_dc
                                                   /\ policy_base' = [ policy_base EXCEPT ![rcv][m.sender] = m.policy ]
                                                   /\ msgs' = msgs \ {m}                                        
                                           /\ DC_state' = [ DC_state EXCEPT ![rcv] = "s4" ]
                                           /\ UNCHANGED << DS_state, received_data >>

RefSend_receive_DC(sndr, rcv, p_i) == /\ DC_state[rcv] = "s2"
                                      /\ \E m \in msgs : 
                                               /\ m.type      = "data"
                                               /\ m.sender    = sndr
                                               /\ m.recepient = rcv                                            
                                               /\ m.policy    = p_i
                                               /\ received_data' = [ received_data EXCEPT ![m.sender][rcv] = m.policy]
                                               /\ msgs' = msgs \ {m}
                                      /\ DC_state' = [ DC_state EXCEPT ![rcv] = "s3"]
                                      /\ UNCHANGED << DS_state, policy_base >>

RefTransfer1_send_DC(sndr, rcv, p_i) == /\ DC_state[sndr] = "s4"
                                        /\ policy_base[sndr][rcv] # "0"
                                        /\ policy_base[sndr][rcv] = p_i
                                        /\ \E d \in Devices : 
                                            << policy_base[sndr][rcv], received_data[d][sndr] >> \in poPolicies
                                        /\ msgs' = msgs \cup { [ type      |-> "data", 
                                                                 sender    |-> sndr, 
                                                                 recepient |-> rcv,
                                                                 policy    |-> policy_base[sndr][rcv] ] }
                                        /\ DC_state' = [ DC_state EXCEPT ![sndr] = "s3" ]
                                        /\ UNCHANGED << DS_state, received_data, policy_base >> 

RefTransfer2_send_DC(sndr, rcv) == /\ DC_state[sndr] = "s4"
                                   /\ policy_base[sndr][rcv] # "0"
                                   /\ \A d \in Devices : 
                                       << policy_base[sndr][rcv], received_data[d][sndr] >> \notin poPolicies                                     
                                   /\ DC_state' = [ DC_state EXCEPT ![sndr] = "s3" ]
                                   /\ UNCHANGED << DS_state, received_data, policy_base, msgs >>

RefNext == \E dc1,dc2 \in DCs : 
               \E p \in Policies :
                   \E ds \in DSs :
                      \* DS events 
                      \/ RefChoose_DS_policy(ds,p)
                      \/ RefRequest_receive_DS(dc1, ds, p)
                      \/ RefSend1_send_DS(ds, dc1, p)
                      \/ RefSend2_send_DS(ds, dc1)
                      \* DC events
                      \/ RefChoose_DC_policy(dc1,p)
                      \/ \E d \in Devices : RefRequest1_send_DC(dc1, d, p)
                      \/ RefRequest2_receive_DC(dc1, dc2, p) 
                      \/ \E d \in Devices : RefSend_receive_DC(d, dc1, p)
                      \/ RefTransfer1_send_DC(dc1, dc2, p)
                      \/ RefTransfer2_send_DC(dc1, dc2)
                

RefDirectPilotSpec == RefInit /\ [][RefNext]_Refvars

INSTANCE pilot

THEOREM RefDirectPilotSpec => SimplePilotSpec

=============================================================================
\* Modification History
\* Last modified Sun Mar 31 19:22:39 CEST 2024 by pardo

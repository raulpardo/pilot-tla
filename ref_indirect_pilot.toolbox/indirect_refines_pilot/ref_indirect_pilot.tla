--------------------- MODULE ref_indirect_pilot ---------------------

(***************************************************************************)
(* This module is a mechanized version of the refinement for indirect      *)
(* communication in the accompanying paper.                                *)
(*                                                                         *)
(* This refinement does not implement the data transfer part.  The reason  *)
(* is that it is identical to the behavior in the spec                     *)
(* `ref_direct_pilot.tla`, which is verified to refine PILOT's semantics.  *)
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
    \cup
    [ type: {"data_broadcast"}, sender: Devices, policy: Policies ]
    \cup
    [ type: {"upload_policy_repo"}, sender: Devices, policy: Policies ]
    \cup
    [ type: {"request_download_policy_repo"}, sender: DSs, DC: DCs ]
    \cup
    [ type: {"reply_download_policy_repo"}, recepient: DSs, DC: DCs, policy: Policies ]

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
    msgs,
        (*******************************************************************)
        (* It models messages in transit.  A device can send a message,    *)
        (* i.e., put a message in the msgs set, or read a message, i.e.,   *)
        (* take a message out of the set.                                  *)
        (*******************************************************************)
    R_state,         \* Current state of the Repository machine
    repo_policy_base \* Policy base of the repository     

IndC_vars == << DS_state, DC_state, policy_base, received_data, msgs, R_state, repo_policy_base >>


IndC_TypeOK == /\ DS_state  \in {"s0", "s1", "s2", "s3", "s4"}                               
               /\ DC_state  \in [ DCs -> {"s0", "s1", "s2", "s3", "s4"} ]
               /\ R_state \in {"s0","s1"}
               /\ repo_policy_base \in [ Devices -> Policies \cup {"0"} ]
               /\ policy_base \in [ Devices -> [ Devices -> Policies \cup {"0"} ] ] \* Ensures one policy per pair of devices
               /\ received_data \in [ Devices -> [ DCs -> Policies \cup {"0"} ] ]
               /\ \A dc \in DCs : received_data[dc][dc] = "0"
               /\ msgs \subseteq Messages

-----------------------------------------------------------------------------

IndC_Init == /\ DS_state      = "s0"         
             /\ DC_state      = [ dc \in DCs |-> "s0" ]
             /\ R_state       = "s0"
             /\ policy_base   = [ d1 \in Devices |-> [ d2 \in Devices |-> "0" ] ]
             /\ received_data = [ d \in Devices |-> [ dc \in DCs |-> "0" ] ]
             /\ repo_policy_base = [ d \in Devices |-> "0" ]
             /\ msgs          = {}
        
-----------------------------------------------------------------------------

(***************************************************************************)
(* Repo events                                                             *)
(***************************************************************************)
IndC_Publish_Policy_receive_Repo(dc,p_dc) == /\ R_state = "s0"
                                             /\ \E m \in msgs : 
                                                    /\ m.type   = "upload_policy_repo"
                                                    /\ m.sender = dc
                                                    /\ m.policy = p_dc
                                                    /\ repo_policy_base' = [ repo_policy_base EXCEPT ![dc] = p_dc ]
                                                    /\ msgs' = msgs \ {m}                                             
                                             /\ UNCHANGED << DC_state, DS_state, policy_base, received_data, R_state >>

IndC_Download_Policies_receive_send_Repo(ds,dc) == /\ R_state = "s0"
                                                   /\ repo_policy_base[dc] # "0"
                                                   /\ \E m \in msgs : 
                                                       /\ m.type   = "request_download_policy_repo"
                                                       /\ m.sender = ds
                                                       /\ m.DC     = dc
                                                       /\ msgs' = (msgs \ {m}) \cup { [ type      |-> "reply_download_policy_repo", 
                                                                                        recepient |-> ds,
                                                                                        DC        |-> dc,
                                                                                        policy    |-> repo_policy_base[dc] ] }
                                                   /\ UNCHANGED << DC_state, DS_state, policy_base, received_data, R_state, repo_policy_base >>
                                                                                        
                                                                             

        
(***************************************************************************)
(* DS device events                                                        *)
(***************************************************************************)

IndC_Choose_DS_policy(ds, p) == /\ DS_state = "s0"
                                /\ policy_base' = [ policy_base EXCEPT ![ds][ds] = p]
                                /\ DS_state' = "s1"
                                /\ UNCHANGED << DC_state, received_data, msgs, R_state, repo_policy_base >>


IndC_Download_Policy_send_DS(ds,dc) == /\ DS_state = "s1"
                                       /\ msgs' = msgs \cup { [ type   |-> "request_download_policy_repo",
                                                                sender |-> ds, 
                                                                DC     |-> dc ] }
                                       /\ DS_state' = "s2"
                                       /\ UNCHANGED << DC_state, policy_base, received_data, R_state, repo_policy_base >>


IndC_Download_Policy_receive_DS(ds,dc) == /\ DS_state  = "s2"
                                          /\ \E m \in msgs :
                                                /\ m.type = "reply_download_policy_repo"                                                       
                                                /\ m.recepient = ds
                                                /\ m.DC        = dc                                                       
                                                /\ policy_base' = [ policy_base EXCEPT ![ds][dc] = m.policy ]
                                                /\ msgs' = msgs \ {m}                                        
                                         /\ DS_state' = "s3"
                                         /\ UNCHANGED << DC_state, received_data, R_state, repo_policy_base >>

IndC_Update_Policies(ds) == /\ DS_state  = "s3"
                            /\ DS_state' = "s1"
                            /\ UNCHANGED << DC_state, received_data, policy_base, msgs, R_state, repo_policy_base >>


IndC_Send_send_DS(sndr, p_i) == /\ DS_state = "s3"
                                     /\ \E rcv \in DCs :
                                        /\ policy_base[sndr][rcv] # "0"
                                        /\ << policy_base[sndr][rcv], policy_base[sndr][sndr] >> \in poPolicies
                                        /\ policy_base[sndr][rcv] = p_i
                                     /\ msgs' = msgs \cup { [ type      |-> "data_broadcast", 
                                                              sender    |-> sndr, 
                                                              recepient |-> rcv,
                                                              policy    |-> p_i ] }                                     
                                     /\ UNCHANGED << DC_state, DS_state, policy_base, received_data, R_state, repo_policy_base >>
                                                    
-----------------------------------------------------------------------------

(***************************************************************************)
(* DC device events                                                        *)
(***************************************************************************)

IndC_Choose_DC_policy(dc, p) == /\ DC_state[dc] = "s0"
                                /\ \A dc1 \in DCs : dc # dc1 => << policy_base[dc1][dc1], p >> \notin poPolicies
                                /\ policy_base' = [ policy_base EXCEPT ![dc][dc] = p]
                                /\ DC_state' = [ DC_state EXCEPT ![dc] = "s1" ]
                                /\ UNCHANGED << DS_state, received_data, msgs, R_state, repo_policy_base >>


IndC_Publish_Policy_send_DC(dc, p_dc) == /\ DC_state[dc] = "s1"
                                         /\ policy_base[dc][dc] # "0"
                                         /\ msgs' = msgs \cup { [ type      |-> "upload_policy_repo", 
                                                                  sender    |-> dc,                                                                  
                                                                  policy    |-> policy_base[dc][dc] ] }
                                         /\ DC_state' = [DC_state EXCEPT ![dc] = "s2" ]
                                         /\ UNCHANGED << DS_state, policy_base, received_data, R_state, repo_policy_base >>




IndC_Send_receive_DC(sndr, rcv, p_i) == /\ DC_state[rcv] = "s2"
                                        /\ \E m \in msgs : 
                                                /\ m.type      = "data_broadcast"
                                                /\ m.sender    = sndr
                                                /\ m.recepient = rcv                                            
                                                /\ m.policy    = p_i                                                
                                                /\ msgs' = msgs \ {m}
                                      /\ <<  policy_base[rcv][rcv], p_i >> \in poPolicies
                                      /\ received_data' = [ received_data EXCEPT ![sndr][rcv] = p_i ]
                                      /\ DC_state' = [ DC_state EXCEPT ![rcv] = "s3"]
                                    /\ UNCHANGED << DS_state, policy_base, R_state, repo_policy_base >>
 


IndC_Next == \E dc1,dc2 \in DCs : 
               \E p \in Policies :
                   \E ds \in DSs :
                      \* DS events 
                      \/ IndC_Choose_DS_policy(ds,p)
                      \/ IndC_Download_Policy_send_DS(ds,dc1)
                      \/ IndC_Download_Policy_receive_DS(ds,dc1)
                      \/ IndC_Send_send_DS(ds, p)
                      \* DC events
                      \/ IndC_Choose_DC_policy(dc1, p)
                      \/ IndC_Publish_Policy_send_DC(dc1, p)
                      \/ IndC_Send_receive_DC(ds, dc1, p)
                      \* Repo Events
                      \/ IndC_Publish_Policy_receive_Repo(dc1,p)
                      \/ IndC_Download_Policies_receive_send_Repo(ds,dc1)
                

IndC_SimplePilotSpec == IndC_Init /\ [][IndC_Next]_IndC_vars

INSTANCE pilot

THEOREM IndC_SimplePilotSpec => SimplePilotSpec
=============================================================================
\* Modification History
\* Last modified Sun Mar 31 19:24:13 CEST 2024 by pardo


theory circus_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm3_ex2 = 
	NID_i0_stm3_ex2 | 
	NID_f0_stm3_ex2 | 
	NID_s0_stm3_ex2 | 
	NID_s1_stm3_ex2



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
 |	
\<comment> \<open>internal_channel_stmbd_stm3_ex2\<close>

internal__stm3_ex2 :: "NIDS_stm3_ex2"
 |	
\<comment> \<open>flowchannel_stmbd_stm3_ex2\<close>

interrupt_stm3_ex2 :: unit 
exited_stm3_ex2 :: unit 
exit_stm3_ex2 :: unit 
 |	
\<comment> \<open>var_channel_stmbd_stm3_ex2\<close>

get_v1 :: "int"
set_v1 :: "int"
setL_v1 :: "int"
setR_v1 :: "int"
 |
get_v :: "int"
set_v :: "int"
setL_v :: "int"
setR_v :: "int"
 |	
\<comment> \<open>event_channel_stmbd_stm3_ex2\<close>

a_in :: unit 
a_out :: unit 
 |
b_in :: unit 
b_out :: unit 
 |
a__in :: "NIDS_stm3_ex2"
 |
b__in :: "NIDS_stm3_ex2"
 |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm3_ex2\<close>

enter_i0_stm3_ex2 :: unit 
interrupt_i0_stm3_ex2 :: unit 
 |	
\<comment> \<open>state_channel_in_stmbd_f0_stm3_ex2\<close>

enter_f0_stm3_ex2 :: unit 
entered_f0_stm3_ex2 :: unit 
interrupt_f0_stm3_ex2 :: unit 
enteredL_f0_stm3_ex2 :: unit 
enteredR_f0_stm3_ex2 :: unit 
 |	
\<comment> \<open>state_channel_in_stmbd_s0_stm3_ex2\<close>

enter_s0_stm3_ex2 :: unit 
entered_s0_stm3_ex2 :: unit 
interrupt_s0_stm3_ex2 :: unit 
enteredL_s0_stm3_ex2 :: unit 
enteredR_s0_stm3_ex2 :: unit 
 |	
\<comment> \<open>state_channel_in_stmbd_s1_stm3_ex2\<close>

enter_s1_stm3_ex2 :: unit 
entered_s1_stm3_ex2 :: unit 
interrupt_s1_stm3_ex2 :: unit 
enteredL_s1_stm3_ex2 :: unit 
enteredR_s1_stm3_ex2 :: unit 
 |	
\<comment> \<open>assumption-guarantee_viol_stm3_ex2\<close>

aviol :: unit 
gviol :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_stm3_ex2 = \<lbrace> 
	  enter_i0_stm3_ex2, 
	  enter_f0_stm3_ex2, 
	  enter_s0_stm3_ex2, 
	  enter_s1_stm3_ex2 \<rbrace>"
	
definition "enteredSS_in_stmbd_stm3_ex2 = \<lbrace> 
	  entered_s1_stm3_ex2, 
	  entered_f0_stm3_ex2, 
	  entered_s0_stm3_ex2 \<rbrace>"
	
definition "internal_events_in_stmbd_stm3_ex2 = \<lbrace> 
	  enter_i0_stm3_ex2, 
	  enter_f0_stm3_ex2, 
	  enter_s0_stm3_ex2, 
	  enter_s1_stm3_ex2, 
	  entered_s1_stm3_ex2, 
	  entered_f0_stm3_ex2, 
	  entered_s0_stm3_ex2, 
	  interrupt_stm3_ex2, 
	  exited_stm3_ex2 \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm3_ex2 = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_stm_stm3_ex2 = \<lbrace> 
	  terminate, 
	  a_in, 
	  a_out, 
	  b_in, 
	  b_out \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
		   "relu x = max 0 x"

definition norm :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
		   "norm x r r' = (((x - fst(r)) / (snd(r) - fst(r))) 
                              * (snd(r') - fst(r'))) + fst(r')"
                              

abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
" InactiveJc_i0_stm3_ex2 = 	(SSTOP \<triangle> (Activation_i0_stm3_ex2
                           	  \<box>
                           	  Termination_i0_stm3_ex2)) "

" Activation_i0_stm3_ex2 = 	(enter_i0_stm3_ex2 \<rightarrow> Active_i0_stm3_ex2) "

" Termination_i0_stm3_ex2 = 	(terminate \<rightarrow> Skip) "

" Active_i0_stm3_ex2 = 	((SSTOP \<triangle> (interrupt_i0_stm3_ex2 \<rightarrow> Skip));; InactiveJc_i0_stm3_ex2) "

" InactiveFn_f0_stm3_ex2 = 	(SSTOP \<triangle> (Activation_f0_stm3_ex2
                           	  \<box>
                           	  Termination_f0_stm3_ex2)) "

" Activation_f0_stm3_ex2 = 	(enter_f0_stm3_ex2 \<rightarrow> Entering_f0_stm3_ex2) "

" Termination_f0_stm3_ex2 = 	(terminate \<rightarrow> Skip) "

" Entering_f0_stm3_ex2 = 	(entered_f0_stm3_ex2 \<rightarrow> Active_f0_stm3_ex2) "

" Active_f0_stm3_ex2 = 	(SSTOP \<triangle> (Termination_f0_stm3_ex2
                       	  \<box>
                       	  (interrupt_f0_stm3_ex2 \<rightarrow> Interrupted_f0_stm3_ex2))) "

" Interrupted_f0_stm3_ex2 = 	(SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> (exited_stm3_ex2 \<rightarrow> InactiveFn_f0_stm3_ex2))) "

" Inactive_s0_stm3_ex2 = 	(SSTOP \<triangle> (Activation_s0_stm3_ex2
                         	  \<box>
                         	  Termination_s0_stm3_ex2)) "

" Activation_s0_stm3_ex2 = 	(enter_s0_stm3_ex2 \<rightarrow> Active_s0_stm3_ex2) "

" Termination_s0_stm3_ex2 = 	(terminate \<rightarrow> Skip) "

" Active_s0_stm3_ex2 = 	((SSTOP \<triangle> (b_out \<rightarrow> Skip));; (Behaviour_s0_stm3_ex2;; Exiting_s0_stm3_ex2)) "

" Behaviour_s0_stm3_ex2 = 	(entered_s0_stm3_ex2 \<rightarrow> During_s0_stm3_ex2) "

" During_s0_stm3_ex2 = 	((Skip;; SSTOP) \<triangle> (interrupt_s0_stm3_ex2 \<rightarrow> Skip)) "

" Exiting_s0_stm3_ex2 = 	((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip));; (Skip;; (exited_stm3_ex2 \<rightarrow> Inactive_s0_stm3_ex2))) "

" Inactive_s1_stm3_ex2 = 	(SSTOP \<triangle> (Activation_s1_stm3_ex2
                         	  \<box>
                         	  Termination_s1_stm3_ex2)) "

" Activation_s1_stm3_ex2 = 	(enter_s1_stm3_ex2 \<rightarrow> Active_s1_stm3_ex2) "

" Termination_s1_stm3_ex2 = 	(terminate \<rightarrow> Skip) "

" Active_s1_stm3_ex2 = 	(Skip;; (Behaviour_s1_stm3_ex2;; Exiting_s1_stm3_ex2)) "

" Behaviour_s1_stm3_ex2 = 	(entered_s1_stm3_ex2 \<rightarrow> During_s1_stm3_ex2) "

" During_s1_stm3_ex2 = 	((Skip;; SSTOP) \<triangle> (interrupt_s1_stm3_ex2 \<rightarrow> Skip)) "

" Exiting_s1_stm3_ex2 = 	((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip));; ((SSTOP \<triangle> (get_v\<^bold>?v \<rightarrow> (assume True (Trans_tbd(n)) (SSTOP \<triangle> (guar True (set_v\<^bold>!(v + 1) \<rightarrow> Skip))))));; (exited_stm3_ex2 \<rightarrow> Inactive_s1_stm3_ex2))) "

" composeNodes_stm3_ex2 = 	(((Inactive_i0_stm3_ex2
                          	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
                          	  Inactive_f0_stm3_ex2)
                          	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
                          	  Inactive_s0_stm3_ex2)
                          	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
                          	  Inactive_s1_stm3_ex2) "

" Trans_stm3_ex2(n) = 	((SSTOP \<triangle> (get_v\<^bold>?v \<rightarrow> (get_v1\<^bold>?v1 \<rightarrow> (assume True (Trans_stm3_ex2(n)) ((((((((n = NID_i0_stm3_ex2) \<^bold>& (((internal__stm3_ex2\<^bold>.NID_i0_stm3_ex2 \<rightarrow> Skip);; (enter_s0_stm3_ex2 \<rightarrow> Trans_stm3_ex2(NID_s0_stm3_ex2)))))
                      	  \<box>
                      	  ((n = NID_s0_stm3_ex2) \<^bold>& ((((v1 \<ge> 1)) \<^bold>& (((internal__stm3_ex2\<^bold>.NID_s0_stm3_ex2 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm3_ex2 \<rightarrow> Skip);; (enter_s1_stm3_ex2 \<rightarrow> Trans_stm3_ex2(NID_s1_stm3_ex2)))))))))))
                      	  \<box>
                      	  ((n = NID_s1_stm3_ex2) \<^bold>& ((((v1 < 1)) \<^bold>& (((internal__stm3_ex2\<^bold>.NID_s1_stm3_ex2 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm3_ex2 \<rightarrow> Skip);; (enter_s0_stm3_ex2 \<rightarrow> Trans_stm3_ex2(NID_s0_stm3_ex2)))))))))))
                      	  \<box>
                      	  ((n = NID_s1_stm3_ex2) \<^bold>& (((a__in\<^bold>.NID_s1_stm3_ex2 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm3_ex2 \<rightarrow> Skip);; (enter_s0_stm3_ex2 \<rightarrow> Trans_stm3_ex2(NID_s0_stm3_ex2)))))))))
                      	  \<box>
                      	  ((n = NID_s1_stm3_ex2) \<^bold>& ((((v > 3)) \<^bold>& (((internal__stm3_ex2\<^bold>.NID_s1_stm3_ex2 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm3_ex2 \<rightarrow> Skip);; (enter_f0_stm3_ex2 \<rightarrow> Trans_stm3_ex2(NID_f0_stm3_ex2)))))))))))
                      	  \<box>
                      	  (share \<rightarrow> Trans_stm3_ex2(n)))
                      	  \<box>
                      	  (((interrupt_stm3_ex2 \<rightarrow> (SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm3_ex2 \<rightarrow> (terminate \<rightarrow> Skip))))
                      	  \<box>
                      	  (terminate \<rightarrow> Skip)))))))) "

" ncCoreBehaviour_stm3_ex2 = 	((((composeNodes_stm3_ex2 [ interrupt_i0_stm3_ex2 \<mapsto> internal__stm3_ex2\<cdot>NID_i0_stm3_ex2,  
                             	 interrupt_s0_stm3_ex2 \<mapsto> internal__stm3_ex2\<cdot>NID_s0_stm3_ex2,  
                             	 interrupt_s1_stm3_ex2 \<mapsto> internal__stm3_ex2\<cdot>NID_s1_stm3_ex2,  
                             	 interrupt_s1_stm3_ex2 \<mapsto> a__in\<cdot>NID_s1_stm3_ex2,  
                             	 interrupt_s1_stm3_ex2 \<mapsto> internal__stm3_ex2\<cdot>NID_s1_stm3_ex2,  
                             	 interrupt_s1_stm3_ex2 \<mapsto> interrupt_stm3_ex2,  
                             	 interrupt_f0_stm3_ex2 \<mapsto> interrupt_stm3_ex2,  
                             	 interrupt_s0_stm3_ex2 \<mapsto> interrupt_stm3_ex2 ]) [ share \<mapsto> share,  
                             	 set_v \<mapsto> setL_v ])
                             	  \<lbrakk> | \<lbrace> exited_stm3_ex2,enter_s0_stm3_ex2,setL_v,enter_s1_stm3_ex2,enter_i0_stm3_ex2,internal__stm3_ex2\<cdot>NID_i0_stm3_ex2,internal__stm3_ex2\<cdot>NID_s1_stm3_ex2,exit_stm3_ex2,a__in\<cdot>NID_s1_stm3_ex2,internal__stm3_ex2\<cdot>NID_s0_stm3_ex2,enter_f0_stm3_ex2,interrupt_stm3_ex2,share,terminate \<rbrace> | \<rbrakk> 
                             	  ((enter_i0_stm3_ex2 \<rightarrow> Trans_stm3_ex2) [ share \<mapsto> share,  
                             	 share \<mapsto> setL_v ])) [ setL_v \<mapsto> set_v ]) "

" ncBehaviour_stm3_ex2 = 	((ncCoreBehaviour_stm3_ex2 \<Zhide> \<lbrace> enter_i0_stm3_ex2,enter_f0_stm3_ex2,enter_s0_stm3_ex2,enter_s1_stm3_ex2,exit_stm3_ex2,exited_stm3_ex2,internal__stm3_ex2 \<rbrace>) [ a__in\<cdot>x \<mapsto> a_in ]) "

" machineBody_stm3_ex2 = 	((ncBehaviour_stm3_ex2
                         	  \<lbrakk> | \<lbrace> interrupt_stm3_ex2 \<rbrace> | \<rbrakk> 
                         	  Skip) \<Zhide> \<lbrace> enteredSS_stm3_ex2 \<rbrace>) "

" Memory_v_stm3_ex2(value) = 	(((get_v_stm3_ex2\<^bold>!value \<rightarrow> Memory_v_stm3_ex2(value))
                             	  \<box>
                             	  ((set_v_stm3_ex2\<^bold>?x__ \<rightarrow> Memory_v_stm3_ex2(x__))
                             	  \<box>
                             	  (terminate \<rightarrow> Skip)))) "

" Memory_v1_stm3_ex2(value) = 	(((get_v1_stm3_ex2\<^bold>!value \<rightarrow> Memory_v1_stm3_ex2(value))
                              	  \<box>
                              	  ((set_v1_stm3_ex2\<^bold>?x__ \<rightarrow> Memory_v1_stm3_ex2(x__))
                              	  \<box>
                              	  (terminate \<rightarrow> Skip)))) "

" varMemory_stm3_ex2 = 	(Memory_v_stm3_ex2(0)
                       	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
                       	  Memory_v1_stm3_ex2(0)) "

" stateful_stm3_ex2 = 	((machineBody_stm3_ex2
                      	  \<lbrakk> | \<lbrace> get_v,set_v1,terminate,get_v1,set_v \<rbrace> | \<rbrakk> 
                      	  varMemory_stm3_ex2) \<Zhide> \<lbrace> get_v,set_v1,terminate,get_v1,set_v \<rbrace>) "

" sharedVarMemory_stm3_ex2 = 	(terminate \<rightarrow> Skip) "

" stm_stm3_ex2 = 	((((((stateful_stm3_ex2 \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [  ])
                 	  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
                 	  Skip)
                 	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
                 	  sharedVarMemory_stm3_ex2) \<Zhide> \<lbrace>  \<rbrace>) "

end



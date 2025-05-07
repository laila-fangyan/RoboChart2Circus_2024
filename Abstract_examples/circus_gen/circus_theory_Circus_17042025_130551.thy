theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm3 = 
	NID_i0_stm3 | 
	NID_s0_stm3 | 
	NID_s1_stm3



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm3\<close>

internal__stm3 :: "NIDS_stm3"
	
\<comment> \<open>flowchannel_stmbd_stm3\<close>

interrupt_stm3 :: unit 
exited_stm3 :: unit 
exit_stm3 :: unit 
	
\<comment> \<open>var_channel_stmbd_stm3\<close>

get_v1 :: "int"
set_v1 :: "int"
setL_v1 :: "int"
setR_v1 :: "int"
	
\<comment> \<open>event_channel_stmbd_stm3\<close>

a_in :: unit 
a_out :: unit 

a__in :: "NIDS_stm3"
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm3\<close>

enter_i0_stm3 :: unit 
interrupt_i0_stm3 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s0_stm3\<close>

enter_s0_stm3 :: unit 
entered_s0_stm3 :: unit 
interrupt_s0_stm3 :: unit 
enteredL_s0_stm3 :: unit 
enteredR_s0_stm3 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s1_stm3\<close>

enter_s1_stm3 :: unit 
entered_s1_stm3 :: unit 
interrupt_s1_stm3 :: unit 
enteredL_s1_stm3 :: unit 
enteredR_s1_stm3 :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_stm3 = \<lbrace> 
	  enter_i0_stm3, 
	  enter_s0_stm3, 
	  enter_s1_stm3 \<rbrace>"
	
definition "enteredSS_in_stmbd_stm3 = \<lbrace> 
	  entered_s0_stm3, 
	  entered_s1_stm3 \<rbrace>"
	
definition "internal_events_in_stmbd_stm3 = \<lbrace> 
	  enter_i0_stm3, 
	  enter_s0_stm3, 
	  enter_s1_stm3, 
	  entered_s0_stm3, 
	  entered_s1_stm3, 
	  interrupt_stm3, 
	  exited_stm3 \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm3 = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_stm_stm3 = \<lbrace> 
	  terminate, 
	  a_in, 
	  a_out \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
		   "relu x = max 0 x"

definition norm :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
		   "norm x r r' = (((x - fst(r)) / (snd(r) - fst(r))) 
                              * (snd(r') - fst(r'))) + fst(r')"
                              
 
actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
" Inactive_i0_stm3 = 
	(SSTOP \<triangle> (Activation_i0_stm3
	  \<box>
	  Termination_i0_stm3)) "

" Activation_i0_stm3 = 
	(enter_i0_stm3 \<rightarrow> Active_i0_stm3) "

" Termination_i0_stm3 = 
	(terminate \<rightarrow> Skip) "

" Active_i0_stm3 = 
	((SSTOP \<triangle> (interrupt_i0_stm3 \<rightarrow> Skip));; Inactive_i0_stm3) "

" Inactive_s0_stm3 = 
	(SSTOP \<triangle> (Activation_s0_stm3
	  \<box>
	  Termination_s0_stm3)) "

" Activation_s0_stm3 = 
	(enter_s0_stm3 \<rightarrow> Active_s0_stm3) "

" Termination_s0_stm3 = 
	(terminate \<rightarrow> Skip) "

" Active_s0_stm3 = 
	(Skip;; (Behaviour_s0_stm3;; Exiting_s0_stm3)) "

" Behaviour_s0_stm3 = 
	(entered_s0_stm3 \<rightarrow> During_s0_stm3) "

" During_s0_stm3 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s0_stm3 \<rightarrow> Skip)) "

" Exiting_s0_stm3 = 
	((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip));; (Skip;; (exited_stm3 \<rightarrow> Inactive_s0_stm3))) "

" Inactive_s1_stm3 = 
	(SSTOP \<triangle> (Activation_s1_stm3
	  \<box>
	  Termination_s1_stm3)) "

" Activation_s1_stm3 = 
	(enter_s1_stm3 \<rightarrow> Active_s1_stm3) "

" Termination_s1_stm3 = 
	(terminate \<rightarrow> Skip) "

" Active_s1_stm3 = 
	(Skip;; (Behaviour_s1_stm3;; Exiting_s1_stm3)) "

" Behaviour_s1_stm3 = 
	(entered_s1_stm3 \<rightarrow> During_s1_stm3) "

" During_s1_stm3 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s1_stm3 \<rightarrow> Skip)) "

" Exiting_s1_stm3 = 
	((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip));; (Skip;; (exited_stm3 \<rightarrow> Inactive_s1_stm3))) "

" composeNodes_stm3 = 
	((Inactive_s1_stm3
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s0_stm3)
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_i0_stm3) "

" Trans_stm3 = 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> ((((((((internal__stm3\<^bold>.NID_i0_stm3 \<rightarrow> Skip);; (enter_s0_stm3 \<rightarrow> Skip))
	  \<box>
	  ((v1 \<ge> 1) \<^bold>& (((internal__stm3\<^bold>.NID_s0_stm3 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip);; (enter_s1_stm3 \<rightarrow> Skip))))))))
	  \<box>
	  ((v1 < 1) \<^bold>& (((internal__stm3\<^bold>.NID_s1_stm3 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip);; (enter_s0_stm3 \<rightarrow> Skip))))))))
	  \<box>
	  ((a__in\<^bold>.NID_s1_stm3 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm3 \<rightarrow> Skip);; (enter_s0_stm3 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip));; Trans_stm3)
	  \<box>
	  (((interrupt_stm3 \<rightarrow> (SSTOP \<triangle> (exit_stm3 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm3 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))))) "

" ncCoreBehaviour_stm3 = 
	(((composeNodes_stm3 [ interrupt_i0_stm3 \<mapsto> internal__stm3\<cdot>NID_i0_stm3,  
	 interrupt_s0_stm3 \<mapsto> internal__stm3\<cdot>NID_s0_stm3,  
	 interrupt_s1_stm3 \<mapsto> internal__stm3\<cdot>NID_s1_stm3,  
	 interrupt_s1_stm3 \<mapsto> a__in\<cdot>NID_s1_stm3,  
	 interrupt_s0_stm3 \<mapsto> interrupt_stm3,  
	 interrupt_s1_stm3 \<mapsto> interrupt_stm3 ]) [ share \<mapsto> share ])
	  \<lbrakk> | \<lbrace> interrupt_stm3,enter_s0_stm3,internal__stm3\<cdot>NID_s0_stm3,enter_s1_stm3,exited_stm3,exit_stm3,internal__stm3\<cdot>NID_i0_stm3,a__in\<cdot>NID_s1_stm3,enter_i0_stm3,share,terminate,internal__stm3\<cdot>NID_s1_stm3 \<rbrace> | \<rbrakk> 
	  ((enter_i0_stm3 \<rightarrow> Trans_stm3) [ share \<mapsto> share ])) "

" ncBehaviour_stm3 = 
	((ncCoreBehaviour_stm3 \<Zhide> \<lbrace> enter_i0_stm3,enter_s0_stm3,enter_s1_stm3,exit_stm3,exited_stm3,internal__stm3 \<rbrace>) [ a__in\<cdot>x \<mapsto> a_in ]) "

" machineBody_stm3 = 
	((ncBehaviour_stm3
	  \<lbrakk> | \<lbrace> interrupt_stm3 \<rbrace> | \<rbrakk> 
	  Skip) \<Zhide> \<lbrace> enteredSS_stm3 \<rbrace>) "

" Memory_v1_stm3 = 
	(((get_v1_stm3\<^bold>!value \<rightarrow> Memory_v1_stm3(value))
	  \<box>
	  ((set_v1_stm3\<^bold>?x__ \<rightarrow> Memory_v1_stm3(x__))
	  \<box>
	  (terminate \<rightarrow> Skip)))) "

" varMemory_stm3 = 
	Memory_v1_stm3(0) "

" stateful_stm3 = 
	((machineBody_stm3
	  \<lbrakk> | \<lbrace> set_v1,terminate,get_v1 \<rbrace> | \<rbrakk> 
	  varMemory_stm3) \<Zhide> \<lbrace> set_v1,terminate,get_v1 \<rbrace>) "

" sharedVarMemory_stm3 = 
	(terminate \<rightarrow> Skip) "

" stm_stm3 = 
	((((((stateful_stm3 \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [  ])
	  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
	  Skip)
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  sharedVarMemory_stm3) \<Zhide> \<lbrace>  \<rbrace>) "

end




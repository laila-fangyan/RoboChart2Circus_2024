theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm0_ex2_ex2 = 
	NID_i0_stm0_ex2_ex2 | 
	NID_s0_stm0_ex2_ex2 | 
	NID_s1_stm0_ex2_ex2



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm0_ex2_ex2\<close>

internal__stm0_ex2_ex2 :: "NIDS_stm0_ex2_ex2"
	
\<comment> \<open>flowchannel_stmbd_stm0_ex2_ex2\<close>

interrupt_stm0_ex2_ex2 :: unit 
exited_stm0_ex2_ex2 :: unit 
exit_stm0_ex2_ex2 :: unit 
	
\<comment> \<open>var_channel_stmbd_stm0_ex2_ex2\<close>

get_v1 :: "int"
set_v1 :: "int"
setL_v1 :: "int"
setR_v1 :: "int"
	
\<comment> \<open>event_channel_stmbd_stm0_ex2_ex2\<close>

a_in :: unit 
a_out :: unit 

a__in :: "NIDS_stm0_ex2_ex2"
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm0_ex2_ex2\<close>

enter_i0_stm0_ex2_ex2 :: unit 
interrupt_i0_stm0_ex2_ex2 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s0_stm0_ex2_ex2\<close>

enter_s0_stm0_ex2_ex2 :: unit 
entered_s0_stm0_ex2_ex2 :: unit 
interrupt_s0_stm0_ex2_ex2 :: unit 
enteredL_s0_stm0_ex2_ex2 :: unit 
enteredR_s0_stm0_ex2_ex2 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s1_stm0_ex2_ex2\<close>

enter_s1_stm0_ex2_ex2 :: unit 
entered_s1_stm0_ex2_ex2 :: unit 
interrupt_s1_stm0_ex2_ex2 :: unit 
enteredL_s1_stm0_ex2_ex2 :: unit 
enteredR_s1_stm0_ex2_ex2 :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_stm0_ex2_ex2 = \<lbrace> 
	  enter_i0_stm0_ex2_ex2, 
	  enter_s0_stm0_ex2_ex2, 
	  enter_s1_stm0_ex2_ex2 \<rbrace>"
	
definition "enteredSS_in_stmbd_stm0_ex2_ex2 = \<lbrace> 
	  entered_s0_stm0_ex2_ex2, 
	  entered_s1_stm0_ex2_ex2 \<rbrace>"
	
definition "internal_events_in_stmbd_stm0_ex2_ex2 = \<lbrace> 
	  enter_i0_stm0_ex2_ex2, 
	  enter_s0_stm0_ex2_ex2, 
	  enter_s1_stm0_ex2_ex2, 
	  entered_s0_stm0_ex2_ex2, 
	  entered_s1_stm0_ex2_ex2, 
	  interrupt_stm0_ex2_ex2, 
	  exited_stm0_ex2_ex2 \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm0_ex2_ex2 = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_stm_stm0_ex2_ex2 = \<lbrace> 
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
" Inactive_i0_stm0_ex2_ex2 = 
	(SSTOP \<triangle> (Activation_i0_stm0_ex2_ex2
	  \<box>
	  Termination_i0_stm0_ex2_ex2)) "

" Activation_i0_stm0_ex2_ex2 = 
	(enter_i0_stm0_ex2_ex2 \<rightarrow> Active_i0_stm0_ex2_ex2) "

" Termination_i0_stm0_ex2_ex2 = 
	(terminate \<rightarrow> Skip) "

" Active_i0_stm0_ex2_ex2 = 
	((SSTOP \<triangle> (interrupt_i0_stm0_ex2_ex2 \<rightarrow> Skip));; Inactive_i0_stm0_ex2_ex2) "

" Inactive_s0_stm0_ex2_ex2 = 
	(SSTOP \<triangle> (Activation_s0_stm0_ex2_ex2
	  \<box>
	  Termination_s0_stm0_ex2_ex2)) "

" Activation_s0_stm0_ex2_ex2 = 
	(enter_s0_stm0_ex2_ex2 \<rightarrow> Active_s0_stm0_ex2_ex2) "

" Termination_s0_stm0_ex2_ex2 = 
	(terminate \<rightarrow> Skip) "

" Active_s0_stm0_ex2_ex2 = 
	(Skip;; (Behaviour_s0_stm0_ex2_ex2;; Exiting_s0_stm0_ex2_ex2)) "

" Behaviour_s0_stm0_ex2_ex2 = 
	(entered_s0_stm0_ex2_ex2 \<rightarrow> During_s0_stm0_ex2_ex2) "

" During_s0_stm0_ex2_ex2 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s0_stm0_ex2_ex2 \<rightarrow> Skip)) "

" Exiting_s0_stm0_ex2_ex2 = 
	((SSTOP \<triangle> (exit_stm0_ex2_ex2 \<rightarrow> Skip));; (Skip;; (exited_stm0_ex2_ex2 \<rightarrow> Inactive_s0_stm0_ex2_ex2))) "

" Inactive_s1_stm0_ex2_ex2 = 
	(SSTOP \<triangle> (Activation_s1_stm0_ex2_ex2
	  \<box>
	  Termination_s1_stm0_ex2_ex2)) "

" Activation_s1_stm0_ex2_ex2 = 
	(enter_s1_stm0_ex2_ex2 \<rightarrow> Active_s1_stm0_ex2_ex2) "

" Termination_s1_stm0_ex2_ex2 = 
	(terminate \<rightarrow> Skip) "

" Active_s1_stm0_ex2_ex2 = 
	(Skip;; (Behaviour_s1_stm0_ex2_ex2;; Exiting_s1_stm0_ex2_ex2)) "

" Behaviour_s1_stm0_ex2_ex2 = 
	(entered_s1_stm0_ex2_ex2 \<rightarrow> During_s1_stm0_ex2_ex2) "

" During_s1_stm0_ex2_ex2 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s1_stm0_ex2_ex2 \<rightarrow> Skip)) "

" Exiting_s1_stm0_ex2_ex2 = 
	((SSTOP \<triangle> (exit_stm0_ex2_ex2 \<rightarrow> Skip));; (Skip;; (exited_stm0_ex2_ex2 \<rightarrow> Inactive_s1_stm0_ex2_ex2))) "

" composeNodes_stm0_ex2_ex2 = 
	((Inactive_s1_stm0_ex2_ex2
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s0_stm0_ex2_ex2)
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_i0_stm0_ex2_ex2) "

" Trans_stm0_ex2_ex2 = 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> ((((((((internal__stm0_ex2_ex2\<^bold>.NID_i0_stm0_ex2_ex2 \<rightarrow> Skip);; (enter_s0_stm0_ex2_ex2 \<rightarrow> Skip))
	  \<box>
	  ((v1 \<ge> 1) \<^bold>& (((internal__stm0_ex2_ex2\<^bold>.NID_s0_stm0_ex2_ex2 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_ex2_ex2 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_ex2_ex2 \<rightarrow> Skip);; (enter_s1_stm0_ex2_ex2 \<rightarrow> Skip))))))))
	  \<box>
	  ((v1 < 1) \<^bold>& (((internal__stm0_ex2_ex2\<^bold>.NID_s1_stm0_ex2_ex2 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_ex2_ex2 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_ex2_ex2 \<rightarrow> Skip);; (enter_s0_stm0_ex2_ex2 \<rightarrow> Skip))))))))
	  \<box>
	  ((a__in\<^bold>.NID_s1_stm0_ex2_ex2 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_ex2_ex2 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_ex2_ex2 \<rightarrow> Skip);; (enter_s0_stm0_ex2_ex2 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip));; Trans_stm0_ex2_ex2)
	  \<box>
	  (((interrupt_stm0_ex2_ex2 \<rightarrow> (SSTOP \<triangle> (exit_stm0_ex2_ex2 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0_ex2_ex2 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))))) "

" ncCoreBehaviour_stm0_ex2_ex2 = 
	(((composeNodes_stm0_ex2_ex2 [ interrupt_i0_stm0_ex2_ex2 \<mapsto> internal__stm0_ex2_ex2\<cdot>NID_i0_stm0_ex2_ex2,  
	 interrupt_s0_stm0_ex2_ex2 \<mapsto> internal__stm0_ex2_ex2\<cdot>NID_s0_stm0_ex2_ex2,  
	 interrupt_s1_stm0_ex2_ex2 \<mapsto> internal__stm0_ex2_ex2\<cdot>NID_s1_stm0_ex2_ex2,  
	 interrupt_s1_stm0_ex2_ex2 \<mapsto> a__in\<cdot>NID_s1_stm0_ex2_ex2,  
	 interrupt_s0_stm0_ex2_ex2 \<mapsto> interrupt_stm0_ex2_ex2,  
	 interrupt_s1_stm0_ex2_ex2 \<mapsto> interrupt_stm0_ex2_ex2 ]) [ share \<mapsto> share ])
	  \<lbrakk> | \<lbrace> enter_s1_stm0_ex2_ex2,exited_stm0_ex2_ex2,interrupt_stm0_ex2_ex2,a__in\<cdot>NID_s1_stm0_ex2_ex2,exit_stm0_ex2_ex2,internal__stm0_ex2_ex2\<cdot>NID_s1_stm0_ex2_ex2,enter_i0_stm0_ex2_ex2,internal__stm0_ex2_ex2\<cdot>NID_s0_stm0_ex2_ex2,share,terminate,enter_s0_stm0_ex2_ex2,internal__stm0_ex2_ex2\<cdot>NID_i0_stm0_ex2_ex2 \<rbrace> | \<rbrakk> 
	  ((enter_i0_stm0_ex2_ex2 \<rightarrow> Trans_stm0_ex2_ex2) [ share \<mapsto> share ])) "

" ncBehaviour_stm0_ex2_ex2 = 
	((ncCoreBehaviour_stm0_ex2_ex2 \<Zhide> \<lbrace> enter_i0_stm0_ex2_ex2,enter_s0_stm0_ex2_ex2,enter_s1_stm0_ex2_ex2,exit_stm0_ex2_ex2,exited_stm0_ex2_ex2,internal__stm0_ex2_ex2 \<rbrace>) [ a__in\<cdot>x \<mapsto> a_in ]) "

" machineBody_stm0_ex2_ex2 = 
	((ncBehaviour_stm0_ex2_ex2
	  \<lbrakk> | \<lbrace> interrupt_stm0_ex2_ex2 \<rbrace> | \<rbrakk> 
	  Skip) \<Zhide> \<lbrace> enteredSS_stm0_ex2_ex2 \<rbrace>) "

" Memory_v1_stm0_ex2_ex2 = 
	(((get_v1_stm0_ex2_ex2\<^bold>!value \<rightarrow> Memory_v1_stm0_ex2_ex2(value))
	  \<box>
	  ((set_v1_stm0_ex2_ex2\<^bold>?x__ \<rightarrow> Memory_v1_stm0_ex2_ex2(x__))
	  \<box>
	  (terminate \<rightarrow> Skip)))) "

" varMemory_stm0_ex2_ex2 = 
	Memory_v1_stm0_ex2_ex2(0) "

" stateful_stm0_ex2_ex2 = 
	((machineBody_stm0_ex2_ex2
	  \<lbrakk> | \<lbrace> set_v1,terminate,get_v1 \<rbrace> | \<rbrakk> 
	  varMemory_stm0_ex2_ex2) \<Zhide> \<lbrace> set_v1,terminate,get_v1 \<rbrace>) "

" sharedVarMemory_stm0_ex2_ex2 = 
	(terminate \<rightarrow> Skip) "

" stm_stm0_ex2_ex2 = 
	((((((stateful_stm0_ex2_ex2 \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [  ])
	  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
	  Skip)
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  sharedVarMemory_stm0_ex2_ex2) \<Zhide> \<lbrace>  \<rbrace>) "

end




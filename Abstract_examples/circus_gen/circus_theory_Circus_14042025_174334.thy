theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm0_ex1 = 
	NID_i0_stm0_ex1 | 
	NID_s0_stm0_ex1 | 
	NID_s1_stm0_ex1 | 
	NID_s2_stm0_ex1



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm0_ex1\<close>

internal__stm0_ex1 :: "NIDS_stm0_ex1"
	
\<comment> \<open>flowchannel_stmbd_stm0_ex1\<close>

interrupt_stm0_ex1 :: unit 
exited_stm0_ex1 :: unit 
exit_stm0_ex1 :: unit 
	
\<comment> \<open>var_channel_stmbd_stm0_ex1\<close>
	
\<comment> \<open>event_channel_stmbd_stm0_ex1\<close>

a_in :: unit 
a_out :: unit 

b_in :: unit 
b_out :: unit 

c_in :: unit 
c_out :: unit 

a__in :: "NIDS_stm0_ex1"

b__in :: "NIDS_stm0_ex1"

c__in :: "NIDS_stm0_ex1"
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm0_ex1\<close>

enter_i0_stm0_ex1 :: unit 
interrupt_i0_stm0_ex1 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s0_stm0_ex1\<close>

enter_s0_stm0_ex1 :: unit 
entered_s0_stm0_ex1 :: unit 
interrupt_s0_stm0_ex1 :: unit 
enteredL_s0_stm0_ex1 :: unit 
enteredR_s0_stm0_ex1 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s1_stm0_ex1\<close>

enter_s1_stm0_ex1 :: unit 
entered_s1_stm0_ex1 :: unit 
interrupt_s1_stm0_ex1 :: unit 
enteredL_s1_stm0_ex1 :: unit 
enteredR_s1_stm0_ex1 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s2_stm0_ex1\<close>

enter_s2_stm0_ex1 :: unit 
entered_s2_stm0_ex1 :: unit 
interrupt_s2_stm0_ex1 :: unit 
enteredL_s2_stm0_ex1 :: unit 
enteredR_s2_stm0_ex1 :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_stm0_ex1 = \<lbrace> 
	  enter_i0_stm0_ex1, 
	  enter_s0_stm0_ex1, 
	  enter_s1_stm0_ex1, 
	  enter_s2_stm0_ex1 \<rbrace>"
	
definition "enteredSS_in_stmbd_stm0_ex1 = \<lbrace> 
	  entered_s2_stm0_ex1, 
	  entered_s1_stm0_ex1, 
	  entered_s0_stm0_ex1 \<rbrace>"
	
definition "internal_events_in_stmbd_stm0_ex1 = \<lbrace> 
	  enter_i0_stm0_ex1, 
	  enter_s0_stm0_ex1, 
	  enter_s1_stm0_ex1, 
	  enter_s2_stm0_ex1, 
	  entered_s2_stm0_ex1, 
	  entered_s1_stm0_ex1, 
	  entered_s0_stm0_ex1, 
	  interrupt_stm0_ex1, 
	  exited_stm0_ex1 \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm0_ex1 = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_stm_stm0_ex1 = \<lbrace> 
	  terminate, 
	  a_in, 
	  a_out, 
	  b_in, 
	  b_out, 
	  c_in, 
	  c_out \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
		   "relu x = max 0 x"

definition norm :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
		   "norm x r r' = (((x - fst(r)) / (snd(r) - fst(r))) 
                              * (snd(r') - fst(r'))) + fst(r')"
                              
 
actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
" Inactive_i0_stm0_ex1 = 
	(SSTOP \<triangle> (Activation_i0_stm0_ex1
	  \<box>
	  Termination_i0_stm0_ex1)) "

" Activation_i0_stm0_ex1 = 
	(enter_i0_stm0_ex1 \<rightarrow> Active_i0_stm0_ex1) "

" Termination_i0_stm0_ex1 = 
	(terminate \<rightarrow> Skip) "

" Active_i0_stm0_ex1 = 
	((SSTOP \<triangle> (interrupt_i0_stm0_ex1 \<rightarrow> Skip));; Inactive_i0_stm0_ex1) "

" Inactive_s0_stm0_ex1 = 
	(SSTOP \<triangle> (Activation_s0_stm0_ex1
	  \<box>
	  Termination_s0_stm0_ex1)) "

" Activation_s0_stm0_ex1 = 
	(enter_s0_stm0_ex1 \<rightarrow> Active_s0_stm0_ex1) "

" Termination_s0_stm0_ex1 = 
	(terminate \<rightarrow> Skip) "

" Active_s0_stm0_ex1 = 
	(Skip;; (Behaviour_s0_stm0_ex1;; Exiting_s0_stm0_ex1)) "

" Behaviour_s0_stm0_ex1 = 
	(entered_s0_stm0_ex1 \<rightarrow> During_s0_stm0_ex1) "

" During_s0_stm0_ex1 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s0_stm0_ex1 \<rightarrow> Skip)) "

" Exiting_s0_stm0_ex1 = 
	((SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip));; (Skip;; (exited_stm0_ex1 \<rightarrow> Inactive_s0_stm0_ex1))) "

" Inactive_s1_stm0_ex1 = 
	(SSTOP \<triangle> (Activation_s1_stm0_ex1
	  \<box>
	  Termination_s1_stm0_ex1)) "

" Activation_s1_stm0_ex1 = 
	(enter_s1_stm0_ex1 \<rightarrow> Active_s1_stm0_ex1) "

" Termination_s1_stm0_ex1 = 
	(terminate \<rightarrow> Skip) "

" Active_s1_stm0_ex1 = 
	(Skip;; (Behaviour_s1_stm0_ex1;; Exiting_s1_stm0_ex1)) "

" Behaviour_s1_stm0_ex1 = 
	(entered_s1_stm0_ex1 \<rightarrow> During_s1_stm0_ex1) "

" During_s1_stm0_ex1 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s1_stm0_ex1 \<rightarrow> Skip)) "

" Exiting_s1_stm0_ex1 = 
	((SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip));; (Skip;; (exited_stm0_ex1 \<rightarrow> Inactive_s1_stm0_ex1))) "

" Inactive_s2_stm0_ex1 = 
	(SSTOP \<triangle> (Activation_s2_stm0_ex1
	  \<box>
	  Termination_s2_stm0_ex1)) "

" Activation_s2_stm0_ex1 = 
	(enter_s2_stm0_ex1 \<rightarrow> Active_s2_stm0_ex1) "

" Termination_s2_stm0_ex1 = 
	(terminate \<rightarrow> Skip) "

" Active_s2_stm0_ex1 = 
	(Skip;; (Behaviour_s2_stm0_ex1;; Exiting_s2_stm0_ex1)) "

" Behaviour_s2_stm0_ex1 = 
	(entered_s2_stm0_ex1 \<rightarrow> During_s2_stm0_ex1) "

" During_s2_stm0_ex1 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s2_stm0_ex1 \<rightarrow> Skip)) "

" Exiting_s2_stm0_ex1 = 
	((SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip));; (Skip;; (exited_stm0_ex1 \<rightarrow> Inactive_s2_stm0_ex1))) "

" composeNodes_stm0_ex1 = 
	(((Inactive_i0_stm0_ex1
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s0_stm0_ex1)
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s2_stm0_ex1)
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s1_stm0_ex1) "

" Trans_stm0_ex1 = 
	((((((((internal__stm0_ex1\<^bold>.NID_i0_stm0_ex1 \<rightarrow> Skip);; (enter_s0_stm0_ex1 \<rightarrow> Skip))
	  \<box>
	  ((a__in\<^bold>.NID_s0_stm0_ex1 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_ex1 \<rightarrow> Skip);; (enter_s1_stm0_ex1 \<rightarrow> Skip))))))
	  \<box>
	  ((b__in\<^bold>.NID_s1_stm0_ex1 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_ex1 \<rightarrow> Skip);; (enter_s0_stm0_ex1 \<rightarrow> Skip))))))
	  \<box>
	  ((c__in\<^bold>.NID_s0_stm0_ex1 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_ex1 \<rightarrow> Skip);; (enter_s2_stm0_ex1 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip));; Trans_stm0_ex1)
	  \<box>
	  (((interrupt_stm0_ex1 \<rightarrow> (SSTOP \<triangle> (exit_stm0_ex1 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0_ex1 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))) "

" ncCoreBehaviour_stm0_ex1 = 
	(((composeNodes_stm0_ex1 [ interrupt_i0_stm0_ex1 \<mapsto> internal__stm0_ex1\<cdot>NID_i0_stm0_ex1,  
	 interrupt_s0_stm0_ex1 \<mapsto> a__in\<cdot>NID_s0_stm0_ex1,  
	 interrupt_s1_stm0_ex1 \<mapsto> b__in\<cdot>NID_s1_stm0_ex1,  
	 interrupt_s0_stm0_ex1 \<mapsto> c__in\<cdot>NID_s0_stm0_ex1,  
	 interrupt_s2_stm0_ex1 \<mapsto> interrupt_stm0_ex1,  
	 interrupt_s1_stm0_ex1 \<mapsto> interrupt_stm0_ex1,  
	 interrupt_s0_stm0_ex1 \<mapsto> interrupt_stm0_ex1 ]) [ share \<mapsto> share ])
	  \<lbrakk> | \<lbrace> internal__stm0_ex1\<cdot>NID_i0_stm0_ex1,a__in\<cdot>NID_s0_stm0_ex1,c__in\<cdot>NID_s0_stm0_ex1,enter_s1_stm0_ex1,enter_s0_stm0_ex1,b__in\<cdot>NID_s1_stm0_ex1,interrupt_stm0_ex1,enter_i0_stm0_ex1,enter_s2_stm0_ex1,exit_stm0_ex1,exited_stm0_ex1,share,terminate \<rbrace> | \<rbrakk> 
	  ((enter_i0_stm0_ex1 \<rightarrow> Trans_stm0_ex1) [ share \<mapsto> share ])) "

" ncBehaviour_stm0_ex1 = 
	((ncCoreBehaviour_stm0_ex1 \<Zhide> \<lbrace> enter_i0_stm0_ex1,enter_s0_stm0_ex1,enter_s1_stm0_ex1,enter_s2_stm0_ex1,exit_stm0_ex1,exited_stm0_ex1,internal__stm0_ex1 \<rbrace>) [ b__in\<cdot>x \<mapsto> b_in,  
	 c__in\<cdot>x \<mapsto> c_in,  
	 a__in\<cdot>x \<mapsto> a_in ]) "

" machineBody_stm0_ex1 = 
	((ncBehaviour_stm0_ex1
	  \<lbrakk> | \<lbrace> interrupt_stm0_ex1 \<rbrace> | \<rbrakk> 
	  Skip) \<Zhide> \<lbrace> enteredSS_stm0_ex1 \<rbrace>) "

" varMemory_stm0_ex1 = 
	(terminate \<rightarrow> Skip) "

" stateful_stm0_ex1 = 
	((machineBody_stm0_ex1
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  varMemory_stm0_ex1) \<Zhide> \<lbrace> terminate \<rbrace>) "

" sharedVarMemory_stm0_ex1 = 
	(terminate \<rightarrow> Skip) "

" stm_stm0_ex1 = 
	((((((stateful_stm0_ex1 \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [  ])
	  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
	  Skip)
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  sharedVarMemory_stm0_ex1) \<Zhide> \<lbrace>  \<rbrace>) "

end




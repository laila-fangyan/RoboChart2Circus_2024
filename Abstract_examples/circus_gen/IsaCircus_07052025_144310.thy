theory circus_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm1 = 
	NID_i0_stm1 | 
	NID_s0_stm1 | 
	NID_s1_stm1 | 
	NID_f0_stm1



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm1\<close>

internal__stm1 :: "NIDS_stm1"
	
\<comment> \<open>flowchannel_stmbd_stm1\<close>

interrupt_stm1 :: unit 
exited_stm1 :: unit 
exit_stm1 :: unit 
	
\<comment> \<open>var_channel_stmbd_stm1\<close>
	
\<comment> \<open>event_channel_stmbd_stm1\<close>

a_in :: unit 
a_out :: unit 

b_in :: unit 
b_out :: unit 

c_in :: unit 
c_out :: unit 

a__in :: "NIDS_stm1"

b__in :: "NIDS_stm1"

c__in :: "NIDS_stm1"
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm1\<close>

enter_i0_stm1 :: unit 
interrupt_i0_stm1 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s0_stm1\<close>

enter_s0_stm1 :: unit 
entered_s0_stm1 :: unit 
interrupt_s0_stm1 :: unit 
enteredL_s0_stm1 :: unit 
enteredR_s0_stm1 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s1_stm1\<close>

enter_s1_stm1 :: unit 
entered_s1_stm1 :: unit 
interrupt_s1_stm1 :: unit 
enteredL_s1_stm1 :: unit 
enteredR_s1_stm1 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_f0_stm1\<close>

enter_f0_stm1 :: unit 
entered_f0_stm1 :: unit 
interrupt_f0_stm1 :: unit 
enteredL_f0_stm1 :: unit 
enteredR_f0_stm1 :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_stm1 = \<lbrace> 
	  enter_i0_stm1, 
	  enter_s0_stm1, 
	  enter_s1_stm1, 
	  enter_f0_stm1 \<rbrace>"
	
definition "enteredSS_in_stmbd_stm1 = \<lbrace> 
	  entered_s1_stm1, 
	  entered_f0_stm1, 
	  entered_s0_stm1 \<rbrace>"
	
definition "internal_events_in_stmbd_stm1 = \<lbrace> 
	  enter_i0_stm1, 
	  enter_s0_stm1, 
	  enter_s1_stm1, 
	  enter_f0_stm1, 
	  entered_s1_stm1, 
	  entered_f0_stm1, 
	  entered_s0_stm1, 
	  interrupt_stm1, 
	  exited_stm1 \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm1 = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_stm_stm1 = \<lbrace> 
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
" Inactive_i0_stm1 = 
	(SSTOP \<triangle> (Activation_i0_stm1
	  \<box>
	  Termination_i0_stm1)) "

" Activation_i0_stm1 = 
	(enter_i0_stm1 \<rightarrow> Active_i0_stm1) "

" Termination_i0_stm1 = 
	(terminate \<rightarrow> Skip) "

" Active_i0_stm1 = 
	((SSTOP \<triangle> (interrupt_i0_stm1 \<rightarrow> Skip));; Inactive_i0_stm1) "

" Inactive_s0_stm1 = 
	(SSTOP \<triangle> (Activation_s0_stm1
	  \<box>
	  Termination_s0_stm1)) "

" Activation_s0_stm1 = 
	(enter_s0_stm1 \<rightarrow> Active_s0_stm1) "

" Termination_s0_stm1 = 
	(terminate \<rightarrow> Skip) "

" Active_s0_stm1 = 
	(Skip;; (Behaviour_s0_stm1;; Exiting_s0_stm1)) "

" Behaviour_s0_stm1 = 
	(entered_s0_stm1 \<rightarrow> During_s0_stm1) "

" During_s0_stm1 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s0_stm1 \<rightarrow> Skip)) "

" Exiting_s0_stm1 = 
	((SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip));; (Skip;; (exited_stm1 \<rightarrow> Inactive_s0_stm1))) "

" Inactive_s1_stm1 = 
	(SSTOP \<triangle> (Activation_s1_stm1
	  \<box>
	  Termination_s1_stm1)) "

" Activation_s1_stm1 = 
	(enter_s1_stm1 \<rightarrow> Active_s1_stm1) "

" Termination_s1_stm1 = 
	(terminate \<rightarrow> Skip) "

" Active_s1_stm1 = 
	(Skip;; (Behaviour_s1_stm1;; Exiting_s1_stm1)) "

" Behaviour_s1_stm1 = 
	(entered_s1_stm1 \<rightarrow> During_s1_stm1) "

" During_s1_stm1 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s1_stm1 \<rightarrow> Skip)) "

" Exiting_s1_stm1 = 
	((SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip));; (Skip;; (exited_stm1 \<rightarrow> Inactive_s1_stm1))) "

" Inactive_f0_stm1 = 
	(SSTOP \<triangle> (Activation_f0_stm1
	  \<box>
	  Termination_f0_stm1)) "

" Activation_f0_stm1 = 
	(enter_f0_stm1 \<rightarrow> Entering_f0_stm1) "

" Termination_f0_stm1 = 
	(terminate \<rightarrow> Skip) "

" Entering_f0_stm1 = 
	(entered_f0_stm1 \<rightarrow> Active_f0_stm1) "

" Active_f0_stm1 = 
	(SSTOP \<triangle> (Termination_f0_stm1
	  \<box>
	  (interrupt_f0_stm1 \<rightarrow> Interrupted_f0_stm1))) "

" Interrupted_f0_stm1 = 
	(SSTOP \<triangle> (exit_stm1 \<rightarrow> (exited_stm1 \<rightarrow> Inactivef0_stm1))) "

" composeNodes_stm1 = 
	(((Inactive_s0_stm1
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s1_stm1)
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_f0_stm1)
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_i0_stm1) "

" Trans_stm1 = 
	(((((((n_ \<^bold>& (((internal__stm1\<^bold>.NID_i0_stm1 \<rightarrow> Skip);; (enter_s0_stm1 \<rightarrow> Trans_stm1(s0_stm1)))))
	  \<box>
	  (n_ \<^bold>& (((a__in\<^bold>.NID_s0_stm1 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm1 \<rightarrow> Skip);; (enter_s1_stm1 \<rightarrow> Trans_stm1(s1_stm1)))))))))
	  \<box>
	  (n_ \<^bold>& (((b__in\<^bold>.NID_s1_stm1 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm1 \<rightarrow> Skip);; (enter_s0_stm1 \<rightarrow> Trans_stm1(s0_stm1)))))))))
	  \<box>
	  (n_ \<^bold>& (((internal__stm1\<^bold>.NID_s1_stm1 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm1 \<rightarrow> Skip);; (enter_f0_stm1 \<rightarrow> Trans_stm1(f0_stm1)))))))))
	  \<box>
	  (share \<rightarrow> Trans_stm1(n)))
	  \<box>
	  (((interrupt_stm1 \<rightarrow> (SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm1 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))) "

" ncCoreBehaviour_stm1 = 
	(((composeNodes_stm1 [ interrupt_i0_stm1 \<mapsto> internal__stm1\<cdot>NID_i0_stm1,  
	 interrupt_s0_stm1 \<mapsto> a__in\<cdot>NID_s0_stm1,  
	 interrupt_s1_stm1 \<mapsto> b__in\<cdot>NID_s1_stm1,  
	 interrupt_s1_stm1 \<mapsto> internal__stm1\<cdot>NID_s1_stm1,  
	 interrupt_s1_stm1 \<mapsto> interrupt_stm1,  
	 interrupt_f0_stm1 \<mapsto> interrupt_stm1,  
	 interrupt_s0_stm1 \<mapsto> interrupt_stm1 ]) [ share \<mapsto> share ])
	  \<lbrakk> | \<lbrace> enter_i0_stm1,b__in\<cdot>NID_s1_stm1,internal__stm1\<cdot>NID_s1_stm1,exited_stm1,enter_f0_stm1,a__in\<cdot>NID_s0_stm1,enter_s0_stm1,interrupt_stm1,exit_stm1,internal__stm1\<cdot>NID_i0_stm1,enter_s1_stm1,share,terminate \<rbrace> | \<rbrakk> 
	  ((enter_i0_stm1 \<rightarrow> Trans_stm1) [ share \<mapsto> share ])) "

" ncBehaviour_stm1 = 
	((ncCoreBehaviour_stm1 \<Zhide> \<lbrace> enter_i0_stm1,enter_s0_stm1,enter_s1_stm1,enter_f0_stm1,exit_stm1,exited_stm1,internal__stm1 \<rbrace>) [ a__in\<cdot>x \<mapsto> a_in,  
	 b__in\<cdot>x \<mapsto> b_in ]) "

" machineBody_stm1 = 
	((ncBehaviour_stm1
	  \<lbrakk> | \<lbrace> interrupt_stm1 \<rbrace> | \<rbrakk> 
	  Skip) \<Zhide> \<lbrace> enteredSS_stm1 \<rbrace>) "

" varMemory_stm1 = 
	(terminate \<rightarrow> Skip) "

" stateful_stm1 = 
	((machineBody_stm1
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  varMemory_stm1) \<Zhide> \<lbrace> terminate \<rbrace>) "

" sharedVarMemory_stm1 = 
	(terminate \<rightarrow> Skip) "

" stm_stm1 = 
	((((((stateful_stm1 \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [  ])
	  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
	  Skip)
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  sharedVarMemory_stm1) \<Zhide> \<lbrace>  \<rbrace>) "

end




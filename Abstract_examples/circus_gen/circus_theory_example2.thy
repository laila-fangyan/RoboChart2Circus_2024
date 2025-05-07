theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm0 = 
	NID_i0_stm0 | 
	NID_s0_stm0 | 
	NID_s1_stm0



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm0\<close>

internal__stm0 :: "NIDS_stm0"
	
\<comment> \<open>flowchannel_stmbd_stm0\<close>

interrupt_stm0 :: unit 
exited_stm0 :: unit 
exit_stm0 :: unit 
	
\<comment> \<open>var_channel_stmbd_stm0\<close>

get_v1 :: "int"
set_v1 :: "int"
setL_v1 :: "int"
setR_v1 :: "int"
	
\<comment> \<open>event_channel_stmbd_stm0\<close>

a_in :: unit 
a_out :: unit 

a__in :: "NIDS_stm0"
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm0\<close>

enter_i0_stm0 :: unit 
interrupt_i0_stm0 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s0_stm0\<close>

enter_s0_stm0 :: unit 
entered_s0_stm0 :: unit 
interrupt_s0_stm0 :: unit 
enteredL_s0_stm0 :: unit 
enteredR_s0_stm0 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s1_stm0\<close>

enter_s1_stm0 :: unit 
entered_s1_stm0 :: unit 
interrupt_s1_stm0 :: unit 
enteredL_s1_stm0 :: unit 
enteredR_s1_stm0 :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_stm0 = \<lbrace> 
	  enter_i0_stm0, 
	  enter_s0_stm0, 
	  enter_s1_stm0 \<rbrace>"
	
definition "enteredSS_in_stmbd_stm0 = \<lbrace> 
	  entered_s1_stm0, 
	  entered_s0_stm0 \<rbrace>"
	
definition "internal_events_in_stmbd_stm0 = \<lbrace> 
	  enter_i0_stm0, 
	  enter_s0_stm0, 
	  enter_s1_stm0, 
	  entered_s1_stm0, 
	  entered_s0_stm0, 
	  interrupt_stm0, 
	  exited_stm0 \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm0 = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_stm_stm0 = \<lbrace> 
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
" Inactive_i0_stm0 = 
	(SSTOP \<triangle> (Activation_i0_stm0
	  \<box>
	  Termination_i0_stm0)) "

" Activation_i0_stm0 = 
	(enter_i0_stm0 \<rightarrow> Active_i0_stm0) "

" Termination_i0_stm0 = 
	(terminate \<rightarrow> Skip) "

" Active_i0_stm0 = 
	((SSTOP \<triangle> (interrupt_i0_stm0 \<rightarrow> Skip));; Inactive_i0_stm0) "

" Inactive_s0_stm0 = 
	(SSTOP \<triangle> (Activation_s0_stm0
	  \<box>
	  Termination_s0_stm0)) "

" Activation_s0_stm0 = 
	(enter_s0_stm0 \<rightarrow> Active_s0_stm0) "

" Termination_s0_stm0 = 
	(terminate \<rightarrow> Skip) "

" Active_s0_stm0 = 
	(Skip;; (Behaviour_s0_stm0;; Exiting_s0_stm0)) "

" Behaviour_s0_stm0 = 
	(entered_s0_stm0 \<rightarrow> During_s0_stm0) "

" During_s0_stm0 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s0_stm0 \<rightarrow> Skip)) "

" Exiting_s0_stm0 = 
	((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (Skip;; (exited_stm0 \<rightarrow> Inactive_s0_stm0))) "

" Inactive_s1_stm0 = 
	(SSTOP \<triangle> (Activation_s1_stm0
	  \<box>
	  Termination_s1_stm0)) "

" Activation_s1_stm0 = 
	(enter_s1_stm0 \<rightarrow> Active_s1_stm0) "

" Termination_s1_stm0 = 
	(terminate \<rightarrow> Skip) "

" Active_s1_stm0 = 
	(Skip;; (Behaviour_s1_stm0;; Exiting_s1_stm0)) "

" Behaviour_s1_stm0 = 
	(entered_s1_stm0 \<rightarrow> During_s1_stm0) "

" During_s1_stm0 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s1_stm0 \<rightarrow> Skip)) "

" Exiting_s1_stm0 = 
	((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (Skip;; (exited_stm0 \<rightarrow> Inactive_s1_stm0))) "

" composeNodes_stm0 = 
	((Inactive_s0_stm0
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s1_stm0)
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_i0_stm0) "

" Trans_stm0 = 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> ((((((((internal__stm0\<^bold>.NID_i0_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))
	  \<box>
	  ((v1 \<ge> 1) \<^bold>& (((internal__stm0\<^bold>.NID_s0_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s1_stm0 \<rightarrow> Skip))))))))
	  \<box>
	  ((v1 < 1) \<^bold>& (((internal__stm0\<^bold>.NID_s1_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))))))))
	  \<box>
	  ((a__in\<^bold>.NID_s1_stm0 \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0 \<rightarrow> Skip);; (enter_s0_stm0 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip));; Trans_stm0)
	  \<box>
	  (((interrupt_stm0 \<rightarrow> (SSTOP \<triangle> (exit_stm0 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))))) "

" ncCoreBehaviour_stm0 = 
	(((composeNodes_stm0 [ interrupt_i0_stm0 \<mapsto> internal__stm0\<cdot>NID_i0_stm0,  
	 interrupt_s0_stm0 \<mapsto> internal__stm0\<cdot>NID_s0_stm0,  
	 interrupt_s1_stm0 \<mapsto> internal__stm0\<cdot>NID_s1_stm0,  
	 interrupt_s1_stm0 \<mapsto> a__in\<cdot>NID_s1_stm0,  
	 interrupt_s1_stm0 \<mapsto> interrupt_stm0,  
	 interrupt_s0_stm0 \<mapsto> interrupt_stm0 ]) [ share \<mapsto> share ])
	  \<lbrakk> | \<lbrace> internal__stm0\<cdot>NID_i0_stm0,interrupt_stm0,internal__stm0\<cdot>NID_s0_stm0,a__in\<cdot>NID_s1_stm0,enter_i0_stm0,internal__stm0\<cdot>NID_s1_stm0,exited_stm0,share,enter_s1_stm0,exit_stm0,terminate,enter_s0_stm0 \<rbrace> | \<rbrakk> 
	  ((enter_i0_stm0 \<rightarrow> Trans_stm0) [ share \<mapsto> share ])) "

" ncBehaviour_stm0 = 
	((ncCoreBehaviour_stm0 \<Zhide> \<lbrace> enter_i0_stm0,enter_s0_stm0,enter_s1_stm0,exit_stm0,exited_stm0,internal__stm0 \<rbrace>) [ a__in\<cdot>x \<mapsto> a_in ]) "

" machineBody_stm0 = 
	((ncBehaviour_stm0
	  \<lbrakk> | \<lbrace> interrupt_stm0 \<rbrace> | \<rbrakk> 
	  Skip) \<Zhide> \<lbrace> enteredSS_stm0 \<rbrace>) "

" Memory_v1_stm0 = 
	(((get_v1_stm0\<^bold>!value \<rightarrow> Memory_v1_stm0(value))
	  \<box>
	  ((set_v1_stm0\<^bold>?x__ \<rightarrow> Memory_v1_stm0(x__))
	  \<box>
	  (terminate \<rightarrow> Skip)))) "

" varMemory_stm0 = 
	Memory_v1_stm0(0) "

" stateful_stm0 = 
	((machineBody_stm0
	  \<lbrakk> | \<lbrace> set_v1,terminate,get_v1 \<rbrace> | \<rbrakk> 
	  varMemory_stm0) \<Zhide> \<lbrace> set_v1,terminate,get_v1 \<rbrace>) "

" sharedVarMemory_stm0 = 
	(terminate \<rightarrow> Skip) "

" stm_stm0 = 
	((((((stateful_stm0 \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [  ])
	  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
	  Skip)
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  sharedVarMemory_stm0) \<Zhide> \<lbrace>  \<rbrace>) "

end




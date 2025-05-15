theory circus_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm4 = 
	NID_i0_stm4 | 
	NID_s0_stm4 | 
	NID_s1_stm4



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm4\<close>

internal__stm4 :: "NIDS_stm4"
	
\<comment> \<open>flowchannel_stmbd_stm4\<close>

interrupt_stm4 :: unit 
exited_stm4 :: unit 
exit_stm4 :: unit 
	
\<comment> \<open>var_channel_stmbd_stm4\<close>

get_v1 :: "int"
set_v1 :: "int"
setL_v1 :: "int"
setR_v1 :: "int"
	
\<comment> \<open>event_channel_stmbd_stm4\<close>

a_in :: unit 
a_out :: unit 

a__in :: "NIDS_stm4"
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm4\<close>

enter_i0_stm4 :: unit 
interrupt_i0_stm4 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s0_stm4\<close>

enter_s0_stm4 :: unit 
entered_s0_stm4 :: unit 
interrupt_s0_stm4 :: unit 
enteredL_s0_stm4 :: unit 
enteredR_s0_stm4 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s1_stm4\<close>

enter_s1_stm4 :: unit 
entered_s1_stm4 :: unit 
interrupt_s1_stm4 :: unit 
enteredL_s1_stm4 :: unit 
enteredR_s1_stm4 :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_stm4 = \<lbrace> 
	  enter_i0_stm4, 
	  enter_s0_stm4, 
	  enter_s1_stm4 \<rbrace>"
	
definition "enteredSS_in_stmbd_stm4 = \<lbrace> 
	  entered_s1_stm4, 
	  entered_s0_stm4 \<rbrace>"
	
definition "internal_events_in_stmbd_stm4 = \<lbrace> 
	  enter_i0_stm4, 
	  enter_s0_stm4, 
	  enter_s1_stm4, 
	  entered_s1_stm4, 
	  entered_s0_stm4, 
	  interrupt_stm4, 
	  exited_stm4 \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm4 = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_stm_stm4 = \<lbrace> 
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
" Inactive_i0_stm4 = 
	(SSTOP \<triangle> (Activation_i0_stm4
	  \<box>
	  Termination_i0_stm4)) "

" Activation_i0_stm4 = 
	(enter_i0_stm4 \<rightarrow> Active_i0_stm4) "

" Termination_i0_stm4 = 
	(terminate \<rightarrow> Skip) "

" Active_i0_stm4 = 
	((SSTOP \<triangle> (interrupt_i0_stm4 \<rightarrow> Skip));; Inactive_i0_stm4) "

" Inactive_s0_stm4 = 
	(SSTOP \<triangle> (Activation_s0_stm4
	  \<box>
	  Termination_s0_stm4)) "

" Activation_s0_stm4 = 
	(enter_s0_stm4 \<rightarrow> Active_s0_stm4) "

" Termination_s0_stm4 = 
	(terminate \<rightarrow> Skip) "

" Active_s0_stm4 = 
	(Skip;; (Behaviour_s0_stm4;; Exiting_s0_stm4)) "

" Behaviour_s0_stm4 = 
	(entered_s0_stm4 \<rightarrow> During_s0_stm4) "

" During_s0_stm4 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s0_stm4 \<rightarrow> Skip)) "

" Exiting_s0_stm4 = 
	((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip));; (Skip;; (exited_stm4 \<rightarrow> Inactive_s0_stm4))) "

" Inactive_s1_stm4 = 
	(SSTOP \<triangle> (Activation_s1_stm4
	  \<box>
	  Termination_s1_stm4)) "

" Activation_s1_stm4 = 
	(enter_s1_stm4 \<rightarrow> Active_s1_stm4) "

" Termination_s1_stm4 = 
	(terminate \<rightarrow> Skip) "

" Active_s1_stm4 = 
	(Skip;; (Behaviour_s1_stm4;; Exiting_s1_stm4)) "

" Behaviour_s1_stm4 = 
	(entered_s1_stm4 \<rightarrow> During_s1_stm4) "

" During_s1_stm4 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s1_stm4 \<rightarrow> Skip)) "

" Exiting_s1_stm4 = 
	((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip));; (Skip;; (exited_stm4 \<rightarrow> Inactive_s1_stm4))) "

" composeNodes_stm4 = 
	((Inactive_s1_stm4
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s0_stm4)
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_i0_stm4) "

" Trans_stm4 = 
	((SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> ))) "

" ncCoreBehaviour_stm4 = 
	(((composeNodes_stm4 [ interrupt_i0_stm4 \<mapsto> internal__stm4\<cdot>NID_i0_stm4,  
	 interrupt_s0_stm4 \<mapsto> internal__stm4\<cdot>NID_s0_stm4,  
	 interrupt_s1_stm4 \<mapsto> internal__stm4\<cdot>NID_s1_stm4,  
	 interrupt_s1_stm4 \<mapsto> a__in\<cdot>NID_s1_stm4,  
	 interrupt_s1_stm4 \<mapsto> interrupt_stm4,  
	 interrupt_s0_stm4 \<mapsto> interrupt_stm4 ]) [ share \<mapsto> share ])
	  \<lbrakk> | \<lbrace> enter_s0_stm4,exited_stm4,interrupt_stm4,enter_s1_stm4,exit_stm4,internal__stm4\<cdot>NID_s0_stm4,a__in\<cdot>NID_s1_stm4,share,enter_i0_stm4,internal__stm4\<cdot>NID_s1_stm4,terminate,internal__stm4\<cdot>NID_i0_stm4 \<rbrace> | \<rbrakk> 
	  ((enter_i0_stm4 \<rightarrow> Trans_stm4) [ share \<mapsto> share ])) "

" ncBehaviour_stm4 = 
	((ncCoreBehaviour_stm4 \<Zhide> \<lbrace> enter_i0_stm4,enter_s0_stm4,enter_s1_stm4,exit_stm4,exited_stm4,internal__stm4 \<rbrace>) [ a__in\<cdot>x \<mapsto> a_in ]) "

" machineBody_stm4 = 
	((ncBehaviour_stm4
	  \<lbrakk> | \<lbrace> interrupt_stm4 \<rbrace> | \<rbrakk> 
	  Skip) \<Zhide> \<lbrace> enteredSS_stm4 \<rbrace>) "

" Memory_v1_stm4 = 
	(((get_v1_stm4\<^bold>!value \<rightarrow> Memory_v1_stm4(value))
	  \<box>
	  ((set_v1_stm4\<^bold>?x__ \<rightarrow> Memory_v1_stm4(x__))
	  \<box>
	  (terminate \<rightarrow> Skip)))) "

" varMemory_stm4 = 
	Memory_v1_stm4(0) "

" stateful_stm4 = 
	((machineBody_stm4
	  \<lbrakk> | \<lbrace> set_v1,terminate,get_v1 \<rbrace> | \<rbrakk> 
	  varMemory_stm4) \<Zhide> \<lbrace> set_v1,terminate,get_v1 \<rbrace>) "

" sharedVarMemory_stm4 = 
	(terminate \<rightarrow> Skip) "

" stm_stm4 = 
	((((((stateful_stm4 \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [  ])
	  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
	  Skip)
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  sharedVarMemory_stm4) \<Zhide> \<lbrace>  \<rbrace>) "

end




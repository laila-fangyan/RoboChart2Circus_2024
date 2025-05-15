theory circus_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm04 = 
	NID_i0_stm04 | 
	NID_s0_stm04 | 
	NID_s1_stm04



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm04\<close>

internal__stm04 :: "NIDS_stm04"
	
\<comment> \<open>flowchannel_stmbd_stm04\<close>

interrupt_stm04 :: unit 
exited_stm04 :: unit 
exit_stm04 :: unit 
	
\<comment> \<open>var_channel_stmbd_stm04\<close>

get_v1 :: "int"
set_v1 :: "int"
setL_v1 :: "int"
setR_v1 :: "int"

get_bl :: "boolean"
set_bl :: "boolean"
setL_bl :: "boolean"
setR_bl :: "boolean"
	
\<comment> \<open>event_channel_stmbd_stm04\<close>

a_in :: unit 
a_out :: unit 

b_in :: unit 
b_out :: unit 

c_in :: unit 
c_out :: unit 

a__in :: "NIDS_stm04"

b__in :: "NIDS_stm04"

c__in :: "NIDS_stm04"
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm04\<close>

enter_i0_stm04 :: unit 
interrupt_i0_stm04 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s0_stm04\<close>

enter_s0_stm04 :: unit 
entered_s0_stm04 :: unit 
interrupt_s0_stm04 :: unit 
enteredL_s0_stm04 :: unit 
enteredR_s0_stm04 :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s1_stm04\<close>

enter_s1_stm04 :: unit 
entered_s1_stm04 :: unit 
interrupt_s1_stm04 :: unit 
enteredL_s1_stm04 :: unit 
enteredR_s1_stm04 :: unit 
	
\<comment> \<open>assumption-guarantee_viol_stm04\<close>

aviol :: unit 
gviol :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_stm04 = \<lbrace> 
	  enter_i0_stm04, 
	  enter_s0_stm04, 
	  enter_s1_stm04 \<rbrace>"
	
definition "enteredSS_in_stmbd_stm04 = \<lbrace> 
	  entered_s0_stm04, 
	  entered_s1_stm04 \<rbrace>"
	
definition "internal_events_in_stmbd_stm04 = \<lbrace> 
	  enter_i0_stm04, 
	  enter_s0_stm04, 
	  enter_s1_stm04, 
	  entered_s0_stm04, 
	  entered_s1_stm04, 
	  interrupt_stm04, 
	  exited_stm04 \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm04 = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_stm_stm04 = \<lbrace> 
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
" Inactive_i0_stm04 = 
	(SSTOP \<triangle> (Activation_i0_stm04
	  \<box>
	  Termination_i0_stm04)) "

" Activation_i0_stm04 = 
	(enter_i0_stm04 \<rightarrow> Active_i0_stm04) "

" Termination_i0_stm04 = 
	(terminate \<rightarrow> Skip) "

" Active_i0_stm04 = 
	((SSTOP \<triangle> (interrupt_i0_stm04 \<rightarrow> Skip));; Inactive_i0_stm04) "

" Inactive_s0_stm04 = 
	(SSTOP \<triangle> (Activation_s0_stm04
	  \<box>
	  Termination_s0_stm04)) "

" Activation_s0_stm04 = 
	(enter_s0_stm04 \<rightarrow> Active_s0_stm04) "

" Termination_s0_stm04 = 
	(terminate \<rightarrow> Skip) "

" Active_s0_stm04 = 
	(Skip;; (Behaviour_s0_stm04;; Exiting_s0_stm04)) "

" Behaviour_s0_stm04 = 
	(entered_s0_stm04 \<rightarrow> During_s0_stm04) "

" During_s0_stm04 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s0_stm04 \<rightarrow> Skip)) "

" Exiting_s0_stm04 = 
	((SSTOP \<triangle> (exit_stm04 \<rightarrow> Skip));; (Skip;; (exited_stm04 \<rightarrow> Inactive_s0_stm04))) "

" Inactive_s1_stm04 = 
	(SSTOP \<triangle> (Activation_s1_stm04
	  \<box>
	  Termination_s1_stm04)) "

" Activation_s1_stm04 = 
	(enter_s1_stm04 \<rightarrow> Active_s1_stm04) "

" Termination_s1_stm04 = 
	(terminate \<rightarrow> Skip) "

" Active_s1_stm04 = 
	(Skip;; (Behaviour_s1_stm04;; Exiting_s1_stm04)) "

" Behaviour_s1_stm04 = 
	(entered_s1_stm04 \<rightarrow> During_s1_stm04) "

" During_s1_stm04 = 
	((Skip;; SSTOP) \<triangle> (interrupt_s1_stm04 \<rightarrow> Skip)) "

" Exiting_s1_stm04 = 
	((SSTOP \<triangle> (exit_stm04 \<rightarrow> Skip));; (Skip;; (exited_stm04 \<rightarrow> Inactive_s1_stm04))) "

" composeNodes_stm04 = 
	((Inactive_i0_stm04
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s0_stm04)
	  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
	  Inactive_s1_stm04) "

" Trans_stm04 = 
	((SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> ))) "

" ncCoreBehaviour_stm04 = 
	(((composeNodes_stm04 [ interrupt_i0_stm04 \<mapsto> internal__stm04\<cdot>NID_i0_stm04,  
	 interrupt_s0_stm04 \<mapsto> internal__stm04\<cdot>NID_s0_stm04,  
	 interrupt_s1_stm04 \<mapsto> internal__stm04\<cdot>NID_s1_stm04,  
	 interrupt_s1_stm04 \<mapsto> a__in\<cdot>NID_s1_stm04,  
	 interrupt_s0_stm04 \<mapsto> interrupt_stm04,  
	 interrupt_s1_stm04 \<mapsto> interrupt_stm04 ]) [ share \<mapsto> share ])
	  \<lbrakk> | \<lbrace> enter_i0_stm04,internal__stm04\<cdot>NID_s0_stm04,interrupt_stm04,internal__stm04\<cdot>NID_s1_stm04,enter_s1_stm04,exited_stm04,share,terminate,enter_s0_stm04,exit_stm04,a__in\<cdot>NID_s1_stm04,internal__stm04\<cdot>NID_i0_stm04 \<rbrace> | \<rbrakk> 
	  ((enter_i0_stm04 \<rightarrow> Trans_stm04) [ share \<mapsto> share ])) "

" ncBehaviour_stm04 = 
	((ncCoreBehaviour_stm04 \<Zhide> \<lbrace> enter_i0_stm04,enter_s0_stm04,enter_s1_stm04,exit_stm04,exited_stm04,internal__stm04 \<rbrace>) [ a__in\<cdot>x \<mapsto> a_in ]) "

" machineBody_stm04 = 
	((ncBehaviour_stm04
	  \<lbrakk> | \<lbrace> interrupt_stm04 \<rbrace> | \<rbrakk> 
	  Skip) \<Zhide> \<lbrace> enteredSS_stm04 \<rbrace>) "

" Memory_bl_stm04 = 
	(((get_bl_stm04\<^bold>!value \<rightarrow> Memory_bl_stm04(value))
	  \<box>
	  ((set_bl_stm04\<^bold>?x__ \<rightarrow> Memory_bl_stm04(x__))
	  \<box>
	  (terminate \<rightarrow> Skip)))) "

" Memory_v1_stm04 = 
	(((get_v1_stm04\<^bold>!value \<rightarrow> Memory_v1_stm04(value))
	  \<box>
	  ((set_v1_stm04\<^bold>?x__ \<rightarrow> Memory_v1_stm04(x__))
	  \<box>
	  (terminate \<rightarrow> Skip)))) "

" varMemory_stm04 = 
	(Memory_bl_stm04(0)
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  Memory_v1_stm04(0)) "

" stateful_stm04 = 
	((machineBody_stm04
	  \<lbrakk> | \<lbrace> set_bl,set_v1,get_bl,terminate,get_v1 \<rbrace> | \<rbrakk> 
	  varMemory_stm04) \<Zhide> \<lbrace> set_bl,set_v1,get_bl,terminate,get_v1 \<rbrace>) "

" sharedVarMemory_stm04 = 
	(terminate \<rightarrow> Skip) "

" stm_stm04 = 
	((((((stateful_stm04 \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [  ])
	  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
	  Skip)
	  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
	  sharedVarMemory_stm04) \<Zhide> \<lbrace>  \<rbrace>) "

end




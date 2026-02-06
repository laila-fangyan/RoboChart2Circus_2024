
theory circus_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm0_ctrl = 
	NID_i0_stm0_ctrl | 
	NID_s0_stm0_ctrl | 
	NID_s1_stm0_ctrl



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
 |	
\<comment> \<open>var_channels_ctrl_ctrl\<close>

get_v1 :: "int"
set_v1 :: "int"
 |	
\<comment> \<open>event_channel_ctrl_ctrl\<close>
 |	
\<comment> \<open>internal_channel_stmbd_stm0_ctrl\<close>

internal__stm0_ctrl :: "NIDS_stm0_ctrl"
 |	
\<comment> \<open>flowchannel_stmbd_stm0_ctrl\<close>

interrupt_stm0_ctrl :: unit 
exited_stm0_ctrl :: unit 
exit_stm0_ctrl :: unit 
 |	
\<comment> \<open>var_channel_stmbd_stm0_ctrl\<close>
 |	
\<comment> \<open>shared_var_channel_stmbd_stm0_ctrl\<close>

set_EXT_v1 :: "int"
 |	
\<comment> \<open>event_channel_stmbd_stm0_ctrl\<close>

a_in :: unit 
a_out :: unit 
 |
a__in :: "NIDS_stm0_ctrl"
 |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm0_ctrl\<close>

enter_i0_stm0_ctrl :: unit 
interrupt_i0_stm0_ctrl :: unit 
 |	
\<comment> \<open>state_channel_in_stmbd_s0_stm0_ctrl\<close>

enter_s0_stm0_ctrl :: unit 
entered_s0_stm0_ctrl :: unit 
interrupt_s0_stm0_ctrl :: unit 
enteredL_s0_stm0_ctrl :: unit 
enteredR_s0_stm0_ctrl :: unit 
 |	
\<comment> \<open>state_channel_in_stmbd_s1_stm0_ctrl\<close>

enter_s1_stm0_ctrl :: unit 
entered_s1_stm0_ctrl :: unit 
interrupt_s1_stm0_ctrl :: unit 
enteredL_s1_stm0_ctrl :: unit 
enteredR_s1_stm0_ctrl :: unit 
 |	
\<comment> \<open>assumption-guarantee_viol_stm0_ctrl\<close>

aviol :: unit 
gviol :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "shared_variable_events_ctrl_ctrl = \<lbrace> 
 \<rbrace>"
	
definition "enterSS_in_stmbd_stm0_ctrl = \<lbrace> 
	  enter_i0_stm0_ctrl, 
	  enter_s0_stm0_ctrl, 
	  enter_s1_stm0_ctrl \<rbrace>"
	
definition "enteredSS_in_stmbd_stm0_ctrl = \<lbrace> 
	  entered_s1_stm0_ctrl, 
	  entered_s0_stm0_ctrl \<rbrace>"
	
definition "internal_events_in_stmbd_stm0_ctrl = \<lbrace> 
	  enter_i0_stm0_ctrl, 
	  enter_s0_stm0_ctrl, 
	  enter_s1_stm0_ctrl, 
	  entered_s1_stm0_ctrl, 
	  entered_s0_stm0_ctrl, 
	  interrupt_stm0_ctrl, 
	  exited_stm0_ctrl \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm0_ctrl = \<lbrace> 
	  set_EXT_v1 \<rbrace>"
	
definition "sem__events_stm_stm0_ctrl = \<lbrace> 
	  terminate, 
	  set_EXT_v1, 
	  a_in, 
	  a_out \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
		   "relu x = max 0 x"

definition norm :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
		   "norm x r r' = (((x - fst(r)) / (snd(r) - fst(r))) 
                              * (snd(r') - fst(r'))) + fst(r')"
                              

locale controller_proc_ctrl
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"Inactive_i0_stm0_ctrl = (SSTOP \<triangle> (Activation_i0_stm0_ctrl
  \<box>
  Termination_i0_stm0_ctrl))" | 

"Activation_i0_stm0_ctrl = (enter_i0_stm0_ctrl \<rightarrow> Active_i0_stm0_ctrl)" | 

"Termination_i0_stm0_ctrl = (terminate \<rightarrow> Skip)" | 

"Active_i0_stm0_ctrl = ((SSTOP \<triangle> (interrupt_i0_stm0_ctrl \<rightarrow> Skip));; Inactive_i0_stm0_ctrl)" | 

"Inactive_s0_stm0_ctrl = (SSTOP \<triangle> (Activation_s0_stm0_ctrl
  \<box>
  Termination_s0_stm0_ctrl))" | 

"Activation_s0_stm0_ctrl = (enter_s0_stm0_ctrl \<rightarrow> Active_s0_stm0_ctrl)" | 

"Termination_s0_stm0_ctrl = (terminate \<rightarrow> Skip)" | 

"Active_s0_stm0_ctrl = (Skip;; (Behaviour_s0_stm0_ctrl;; Exiting_s0_stm0_ctrl))" | 

"Behaviour_s0_stm0_ctrl = (entered_s0_stm0_ctrl \<rightarrow> During_s0_stm0_ctrl)" | 

"During_s0_stm0_ctrl = ((Skip;; SSTOP) \<triangle> (interrupt_s0_stm0_ctrl \<rightarrow> Skip))" | 

"Exiting_s0_stm0_ctrl = ((SSTOP \<triangle> (exit_stm0_ctrl \<rightarrow> Skip));; (Skip;; (exited_stm0_ctrl \<rightarrow> Inactive_s0_stm0_ctrl)))" | 

"Inactive_s1_stm0_ctrl = (SSTOP \<triangle> (Activation_s1_stm0_ctrl
  \<box>
  Termination_s1_stm0_ctrl))" | 

"Activation_s1_stm0_ctrl = (enter_s1_stm0_ctrl \<rightarrow> Active_s1_stm0_ctrl)" | 

"Termination_s1_stm0_ctrl = (terminate \<rightarrow> Skip)" | 

"Active_s1_stm0_ctrl = (Skip;; (Behaviour_s1_stm0_ctrl;; Exiting_s1_stm0_ctrl))" | 

"Behaviour_s1_stm0_ctrl = (entered_s1_stm0_ctrl \<rightarrow> During_s1_stm0_ctrl)" | 

"During_s1_stm0_ctrl = ((Skip;; SSTOP) \<triangle> (interrupt_s1_stm0_ctrl \<rightarrow> Skip))" | 

"Exiting_s1_stm0_ctrl = ((SSTOP \<triangle> (exit_stm0_ctrl \<rightarrow> Skip));; (Skip;; (exited_stm0_ctrl \<rightarrow> Inactive_s1_stm0_ctrl)))" | 

"composeNodes_stm0_ctrl = ((Inactive_s0_stm0_ctrl
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_s1_stm0_ctrl)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_i0_stm0_ctrl)" | 

"Trans_stm0_ctrl(n :: NIDS_stm0_ctrl) = ((SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (assume True (Trans_stm0_ctrl(n)) ((((((n = NID_i0_stm0_ctrl) \<^bold>& (((internal__stm0_ctrl\<^bold>.NID_i0_stm0_ctrl \<rightarrow> (SSTOP \<triangle> (guar True (set_v1\<^bold>!2 \<rightarrow> Skip))));; (enter_s0_stm0_ctrl \<rightarrow> Trans_stm0_ctrl(NID_s0_stm0_ctrl)))))
  \<box>
  ((n = NID_s0_stm0_ctrl) \<^bold>& ((((v1 \<ge> 1)) \<^bold>& (((internal__stm0_ctrl\<^bold>.NID_s0_stm0_ctrl \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_ctrl \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_ctrl \<rightarrow> (SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (assume True (Trans_tbd(n)) (SSTOP \<triangle> (guar True (set_v1\<^bold>!(v1 - 2) \<rightarrow> Skip)))))));; (enter_s1_stm0_ctrl \<rightarrow> Trans_stm0_ctrl(NID_s1_stm0_ctrl)))))))))))
  \<box>
  ((n = NID_s1_stm0_ctrl) \<^bold>& (((a__in\<^bold>.NID_s1_stm0_ctrl \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_ctrl \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_ctrl \<rightarrow> Skip);; (enter_s0_stm0_ctrl \<rightarrow> Trans_stm0_ctrl(NID_s0_stm0_ctrl)))))))))
  \<box>
  (share \<rightarrow> Trans_stm0_ctrl(n)))
  \<box>
  (((interrupt_stm0_ctrl \<rightarrow> (SSTOP \<triangle> (exit_stm0_ctrl \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0_ctrl \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip)))))))" | 

"ncCoreBehaviour_stm0_ctrl = (((composeNodes_stm0_ctrl [ interrupt_i0_stm0_ctrl \<mapsto> internal__stm0_ctrl\<cdot>NID_i0_stm0_ctrl,  
 interrupt_s0_stm0_ctrl \<mapsto> internal__stm0_ctrl\<cdot>NID_s0_stm0_ctrl,  
 interrupt_s1_stm0_ctrl \<mapsto> a__in\<cdot>NID_s1_stm0_ctrl,  
 interrupt_s1_stm0_ctrl \<mapsto> interrupt_stm0_ctrl,  
 interrupt_s0_stm0_ctrl \<mapsto> interrupt_stm0_ctrl ]) [ share \<mapsto> share ])
  \<lbrakk> | \<lbrace> enter_s1_stm0_ctrl,interrupt_stm0_ctrl,enter_i0_stm0_ctrl,internal__stm0_ctrl\<cdot>NID_i0_stm0_ctrl,share,terminate,enter_s0_stm0_ctrl,exit_stm0_ctrl,a__in\<cdot>NID_s1_stm0_ctrl,exited_stm0_ctrl,internal__stm0_ctrl\<cdot>NID_s0_stm0_ctrl \<rbrace> | \<rbrakk> 
  ((enter_i0_stm0_ctrl \<rightarrow> Trans_stm0_ctrl) [ share \<mapsto> share ]))" | 

"ncBehaviour_stm0_ctrl = ((ncCoreBehaviour_stm0_ctrl \<Zhide> \<lbrace> enter_i0_stm0_ctrl,enter_s0_stm0_ctrl,enter_s1_stm0_ctrl,exit_stm0_ctrl,exited_stm0_ctrl,internal__stm0_ctrl \<rbrace>) [ a__in\<cdot>x \<mapsto> a_in ])" | 

"machineBody_stm0_ctrl = ((ncBehaviour_stm0_ctrl
  \<lbrakk> | \<lbrace> interrupt_stm0_ctrl \<rbrace> | \<rbrakk> 
  Skip) \<Zhide> \<lbrace> enteredSS_stm0_ctrl \<rbrace>)" | 

"varMemory_stm0_ctrl = (terminate \<rightarrow> Skip)" | 

"stateful_stm0_ctrl = ((machineBody_stm0_ctrl
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  varMemory_stm0_ctrl) \<Zhide> \<lbrace> terminate \<rbrace>)" | 

"sharedMemory_v1(value :: int) = (((get_v1\<^bold>!value \<rightarrow> sharedMemory_v1(value))
  \<box>
  ((set_v1\<^bold>?x__ \<rightarrow> sharedMemory_v1(x__))
  \<box>
  ((set_EXT_v1\<^bold>?x__ \<rightarrow> sharedMemory_v1(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedVarMemory_stm0_ctrl = sharedMemory_v1(0)" | 

"stm_stm0_ctrl = ((((((stateful_stm0_ctrl \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [ share \<mapsto> set_EXT_v1 ])
  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
  Skip)
  \<lbrakk> | \<lbrace> set_EXT_v1,set_v1,terminate,get_v1 \<rbrace> | \<rbrakk> 
  sharedVarMemory_stm0_ctrl) \<Zhide> \<lbrace> get_v1 \<rbrace>)" | 

"composeMachines_ctrl = (stm_stm0_ctrl [  ])" | 

"crtlMemory_ctrl(v1 :: int) = (((set_v1\<^bold>?x__ \<rightarrow> ctrlMemory_ctrl(x__))
  \<box>
  (terminate \<rightarrow> Skip)))" | 

"controller_action_ctrl = ((composeMachines_ctrl
  \<lbrakk> | \<lbrace> set_v1,terminate \<rbrace> | \<rbrakk> 
  crtlMemory_ctrl(0)) \<Zhide> \<lbrace> set_v1 \<rbrace>)"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess controller_action_ctrl"

end




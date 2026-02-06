
theory circus_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm0_robot_ctrl = 
	NID_i0_stm0_robot_ctrl | 
	NID_detect_stm0_robot_ctrl | 
	NID_stop_stm0_robot_ctrl | 
	NID_move_stm0_robot_ctrl | 
	NID_f0_stm0_robot_ctrl


\<comment> \<open>constant and function declaration/definition\<close>
consts dest :: "nat"
	

\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
 |	
\<comment> \<open>var_channels_ctrl_robot_ctrl\<close>

get_obs :: "int"
set_obs :: "int"
 |	
\<comment> \<open>event_channel_ctrl_robot_ctrl\<close>
 |	
\<comment> \<open>internal_channel_stmbd_stm0_robot_ctrl\<close>

internal__stm0_robot_ctrl :: "NIDS_stm0_robot_ctrl"
 |	
\<comment> \<open>flowchannel_stmbd_stm0_robot_ctrl\<close>

interrupt_stm0_robot_ctrl :: unit 
exited_stm0_robot_ctrl :: unit 
exit_stm0_robot_ctrl :: unit 
 |	
\<comment> \<open>var_channel_stmbd_stm0_robot_ctrl\<close>

get_pos :: "nat"
set_pos :: "nat"
setL_pos :: "nat"
setR_pos :: "nat"
 |	
\<comment> \<open>shared_var_channel_stmbd_stm0_robot_ctrl\<close>

set_EXT_obs :: "int"
 |	
\<comment> \<open>event_channel_stmbd_stm0_robot_ctrl\<close>

arrival_in :: unit 
arrival_out :: unit 
 |
arrival__in :: "NIDS_stm0_robot_ctrl"
 |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm0_robot_ctrl\<close>

enter_i0_stm0_robot_ctrl :: unit 
interrupt_i0_stm0_robot_ctrl :: unit 
 |	
\<comment> \<open>state_channel_in_stmbd_detect_stm0_robot_ctrl\<close>

enter_detect_stm0_robot_ctrl :: unit 
entered_detect_stm0_robot_ctrl :: unit 
interrupt_detect_stm0_robot_ctrl :: unit 
enteredL_detect_stm0_robot_ctrl :: unit 
enteredR_detect_stm0_robot_ctrl :: unit 
 |	
\<comment> \<open>state_channel_in_stmbd_stop_stm0_robot_ctrl\<close>

enter_stop_stm0_robot_ctrl :: unit 
entered_stop_stm0_robot_ctrl :: unit 
interrupt_stop_stm0_robot_ctrl :: unit 
enteredL_stop_stm0_robot_ctrl :: unit 
enteredR_stop_stm0_robot_ctrl :: unit 
 |	
\<comment> \<open>state_channel_in_stmbd_move_stm0_robot_ctrl\<close>

enter_move_stm0_robot_ctrl :: unit 
entered_move_stm0_robot_ctrl :: unit 
interrupt_move_stm0_robot_ctrl :: unit 
enteredL_move_stm0_robot_ctrl :: unit 
enteredR_move_stm0_robot_ctrl :: unit 
 |	
\<comment> \<open>state_channel_in_stmbd_f0_stm0_robot_ctrl\<close>

enter_f0_stm0_robot_ctrl :: unit 
entered_f0_stm0_robot_ctrl :: unit 
interrupt_f0_stm0_robot_ctrl :: unit 
enteredL_f0_stm0_robot_ctrl :: unit 
enteredR_f0_stm0_robot_ctrl :: unit 
 |	
\<comment> \<open>assumption-guarantee_viol_stm0_robot_ctrl\<close>

aviol :: unit 
gviol :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "shared_variable_events_ctrl_robot_ctrl = \<lbrace> 
 \<rbrace>"
	
definition "enterSS_in_stmbd_stm0_robot_ctrl = \<lbrace> 
	  enter_i0_stm0_robot_ctrl, 
	  enter_detect_stm0_robot_ctrl, 
	  enter_stop_stm0_robot_ctrl, 
	  enter_move_stm0_robot_ctrl, 
	  enter_f0_stm0_robot_ctrl \<rbrace>"
	
definition "enteredSS_in_stmbd_stm0_robot_ctrl = \<lbrace> 
	  entered_f0_stm0_robot_ctrl, 
	  entered_detect_stm0_robot_ctrl, 
	  entered_stop_stm0_robot_ctrl, 
	  entered_move_stm0_robot_ctrl \<rbrace>"
	
definition "internal_events_in_stmbd_stm0_robot_ctrl = \<lbrace> 
	  enter_i0_stm0_robot_ctrl, 
	  enter_detect_stm0_robot_ctrl, 
	  enter_stop_stm0_robot_ctrl, 
	  enter_move_stm0_robot_ctrl, 
	  enter_f0_stm0_robot_ctrl, 
	  entered_f0_stm0_robot_ctrl, 
	  entered_detect_stm0_robot_ctrl, 
	  entered_stop_stm0_robot_ctrl, 
	  entered_move_stm0_robot_ctrl, 
	  interrupt_stm0_robot_ctrl, 
	  exited_stm0_robot_ctrl \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm0_robot_ctrl = \<lbrace> 
	  set_EXT_obs \<rbrace>"
	
definition "sem__events_stm_stm0_robot_ctrl = \<lbrace> 
	  terminate, 
	  set_EXT_obs, 
	  arrival_in, 
	  arrival_out \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
		   "relu x = max 0 x"

definition norm :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
		   "norm x r r' = (((x - fst(r)) / (snd(r) - fst(r))) 
                              * (snd(r') - fst(r'))) + fst(r')"
                              

locale controller_proc_robot_ctrl
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"Inactive_i0_stm0_robot_ctrl = (SSTOP \<triangle> (Activation_i0_stm0_robot_ctrl
  \<box>
  Termination_i0_stm0_robot_ctrl))" | 

"Activation_i0_stm0_robot_ctrl = (enter_i0_stm0_robot_ctrl \<rightarrow> Active_i0_stm0_robot_ctrl)" | 

"Termination_i0_stm0_robot_ctrl = (terminate \<rightarrow> Skip)" | 

"Active_i0_stm0_robot_ctrl = ((SSTOP \<triangle> (interrupt_i0_stm0_robot_ctrl \<rightarrow> Skip));; Inactive_i0_stm0_robot_ctrl)" | 

"Inactive_detect_stm0_robot_ctrl = (SSTOP \<triangle> (Activation_detect_stm0_robot_ctrl
  \<box>
  Termination_detect_stm0_robot_ctrl))" | 

"Activation_detect_stm0_robot_ctrl = (enter_detect_stm0_robot_ctrl \<rightarrow> Active_detect_stm0_robot_ctrl)" | 

"Termination_detect_stm0_robot_ctrl = (terminate \<rightarrow> Skip)" | 

"Active_detect_stm0_robot_ctrl = (Skip;; (Behaviour_detect_stm0_robot_ctrl;; Exiting_detect_stm0_robot_ctrl))" | 

"Behaviour_detect_stm0_robot_ctrl = (entered_detect_stm0_robot_ctrl \<rightarrow> During_detect_stm0_robot_ctrl)" | 

"During_detect_stm0_robot_ctrl = ((Skip;; SSTOP) \<triangle> (interrupt_detect_stm0_robot_ctrl \<rightarrow> Skip))" | 

"Exiting_detect_stm0_robot_ctrl = ((SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> Skip));; (Skip;; (exited_stm0_robot_ctrl \<rightarrow> Inactive_detect_stm0_robot_ctrl)))" | 

"Inactive_stop_stm0_robot_ctrl = (SSTOP \<triangle> (Activation_stop_stm0_robot_ctrl
  \<box>
  Termination_stop_stm0_robot_ctrl))" | 

"Activation_stop_stm0_robot_ctrl = (enter_stop_stm0_robot_ctrl \<rightarrow> Active_stop_stm0_robot_ctrl)" | 

"Termination_stop_stm0_robot_ctrl = (terminate \<rightarrow> Skip)" | 

"Active_stop_stm0_robot_ctrl = (Skip;; (Behaviour_stop_stm0_robot_ctrl;; Exiting_stop_stm0_robot_ctrl))" | 

"Behaviour_stop_stm0_robot_ctrl = (entered_stop_stm0_robot_ctrl \<rightarrow> During_stop_stm0_robot_ctrl)" | 

"During_stop_stm0_robot_ctrl = ((Skip;; SSTOP) \<triangle> (interrupt_stop_stm0_robot_ctrl \<rightarrow> Skip))" | 

"Exiting_stop_stm0_robot_ctrl = ((SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> Skip));; (Skip;; (exited_stm0_robot_ctrl \<rightarrow> Inactive_stop_stm0_robot_ctrl)))" | 

"Inactive_move_stm0_robot_ctrl = (SSTOP \<triangle> (Activation_move_stm0_robot_ctrl
  \<box>
  Termination_move_stm0_robot_ctrl))" | 

"Activation_move_stm0_robot_ctrl = (enter_move_stm0_robot_ctrl \<rightarrow> Active_move_stm0_robot_ctrl)" | 

"Termination_move_stm0_robot_ctrl = (terminate \<rightarrow> Skip)" | 

"Active_move_stm0_robot_ctrl = (Skip;; (Behaviour_move_stm0_robot_ctrl;; Exiting_move_stm0_robot_ctrl))" | 

"Behaviour_move_stm0_robot_ctrl = (entered_move_stm0_robot_ctrl \<rightarrow> During_move_stm0_robot_ctrl)" | 

"During_move_stm0_robot_ctrl = ((Skip;; SSTOP) \<triangle> (interrupt_move_stm0_robot_ctrl \<rightarrow> Skip))" | 

"Exiting_move_stm0_robot_ctrl = ((SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> Skip));; (Skip;; (exited_stm0_robot_ctrl \<rightarrow> Inactive_move_stm0_robot_ctrl)))" | 

"Inactive_f0_stm0_robot_ctrl = (SSTOP \<triangle> (Activation_f0_stm0_robot_ctrl
  \<box>
  Termination_f0_stm0_robot_ctrl))" | 

"Activation_f0_stm0_robot_ctrl = (enter_f0_stm0_robot_ctrl \<rightarrow> Entering_f0_stm0_robot_ctrl)" | 

"Termination_f0_stm0_robot_ctrl = (terminate \<rightarrow> Skip)" | 

"Entering_f0_stm0_robot_ctrl = (entered_f0_stm0_robot_ctrl \<rightarrow> Active_f0_stm0_robot_ctrl)" | 

"Active_f0_stm0_robot_ctrl = (SSTOP \<triangle> (Termination_f0_stm0_robot_ctrl
  \<box>
  (interrupt_f0_stm0_robot_ctrl \<rightarrow> Interrupted_f0_stm0_robot_ctrl)))" | 

"Interrupted_f0_stm0_robot_ctrl = (SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> (exited_stm0_robot_ctrl \<rightarrow> Inactivef0_stm0_robot_ctrl)))" | 

"composeNodes_stm0_robot_ctrl = ((((Inactive_detect_stm0_robot_ctrl
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_move_stm0_robot_ctrl)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_stop_stm0_robot_ctrl)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_i0_stm0_robot_ctrl)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_f0_stm0_robot_ctrl)" | 

"Trans_stm0_robot_ctrl(n :: NIDS_stm0_robot_ctrl) = ((SSTOP \<triangle> (get_obs\<^bold>?obs \<rightarrow> (get_pos\<^bold>?pos \<rightarrow> (assume True (Trans_stm0_robot_ctrl(n)) (((((((((n = NID_i0_stm0_robot_ctrl) \<^bold>& (((internal__stm0_robot_ctrl\<^bold>.NID_i0_stm0_robot_ctrl \<rightarrow> Skip);; (enter_detect_stm0_robot_ctrl \<rightarrow> Trans_stm0_robot_ctrl(NID_detect_stm0_robot_ctrl)))))
  \<box>
  ((n = NID_detect_stm0_robot_ctrl) \<^bold>& ((((obs = 1)) \<^bold>& (((internal__stm0_robot_ctrl\<^bold>.NID_detect_stm0_robot_ctrl \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_robot_ctrl \<rightarrow> Skip);; (enter_stop_stm0_robot_ctrl \<rightarrow> Trans_stm0_robot_ctrl(NID_stop_stm0_robot_ctrl)))))))))))
  \<box>
  ((n = NID_stop_stm0_robot_ctrl) \<^bold>& (((internal__stm0_robot_ctrl\<^bold>.NID_stop_stm0_robot_ctrl \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_robot_ctrl \<rightarrow> Skip);; (enter_f0_stm0_robot_ctrl \<rightarrow> Trans_stm0_robot_ctrl(NID_f0_stm0_robot_ctrl)))))))))
  \<box>
  ((n = NID_move_stm0_robot_ctrl) \<^bold>& ((((pos = dest)) \<^bold>& (((internal__stm0_robot_ctrl\<^bold>.NID_move_stm0_robot_ctrl \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_robot_ctrl \<rightarrow> (SSTOP \<triangle> (arrival_out \<rightarrow> Skip)));; (enter_stop_stm0_robot_ctrl \<rightarrow> Trans_stm0_robot_ctrl(NID_stop_stm0_robot_ctrl)))))))))))
  \<box>
  ((n = NID_detect_stm0_robot_ctrl) \<^bold>& ((((obs = (-1))) \<^bold>& (((internal__stm0_robot_ctrl\<^bold>.NID_detect_stm0_robot_ctrl \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_robot_ctrl \<rightarrow> Skip);; (enter_move_stm0_robot_ctrl \<rightarrow> Trans_stm0_robot_ctrl(NID_move_stm0_robot_ctrl)))))))))))
  \<box>
  ((n = NID_move_stm0_robot_ctrl) \<^bold>& ((((pos < dest)) \<^bold>& (((internal__stm0_robot_ctrl\<^bold>.NID_move_stm0_robot_ctrl \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_robot_ctrl \<rightarrow> (SSTOP \<triangle> (get_pos\<^bold>?pos \<rightarrow> (assume True ((SSTOP \<triangle> (guar True (set_pos\<^bold>!(pos + 1) \<rightarrow> Skip)))) (SSTOP \<triangle> (guar True (set_pos\<^bold>!(pos + 1) \<rightarrow> Skip)))))));; (enter_detect_stm0_robot_ctrl \<rightarrow> Trans_stm0_robot_ctrl(NID_detect_stm0_robot_ctrl)))))))))))
  \<box>
  (share \<rightarrow> Trans_stm0_robot_ctrl(n)))
  \<box>
  (((interrupt_stm0_robot_ctrl \<rightarrow> (SSTOP \<triangle> (exit_stm0_robot_ctrl \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0_robot_ctrl \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip))))))))" | 

"ncCoreBehaviour_stm0_robot_ctrl = (((composeNodes_stm0_robot_ctrl [ interrupt_i0_stm0_robot_ctrl \<mapsto> internal__stm0_robot_ctrl\<cdot>NID_i0_stm0_robot_ctrl,  
 interrupt_detect_stm0_robot_ctrl \<mapsto> internal__stm0_robot_ctrl\<cdot>NID_detect_stm0_robot_ctrl,  
 interrupt_stop_stm0_robot_ctrl \<mapsto> internal__stm0_robot_ctrl\<cdot>NID_stop_stm0_robot_ctrl,  
 interrupt_move_stm0_robot_ctrl \<mapsto> internal__stm0_robot_ctrl\<cdot>NID_move_stm0_robot_ctrl,  
 interrupt_detect_stm0_robot_ctrl \<mapsto> internal__stm0_robot_ctrl\<cdot>NID_detect_stm0_robot_ctrl,  
 interrupt_move_stm0_robot_ctrl \<mapsto> internal__stm0_robot_ctrl\<cdot>NID_move_stm0_robot_ctrl,  
 interrupt_f0_stm0_robot_ctrl \<mapsto> interrupt_stm0_robot_ctrl,  
 interrupt_detect_stm0_robot_ctrl \<mapsto> interrupt_stm0_robot_ctrl,  
 interrupt_stop_stm0_robot_ctrl \<mapsto> interrupt_stm0_robot_ctrl,  
 interrupt_move_stm0_robot_ctrl \<mapsto> interrupt_stm0_robot_ctrl ]) [ share \<mapsto> share ])
  \<lbrakk> | \<lbrace> enter_f0_stm0_robot_ctrl,interrupt_stm0_robot_ctrl,enter_detect_stm0_robot_ctrl,exited_stm0_robot_ctrl,exit_stm0_robot_ctrl,internal__stm0_robot_ctrl\<cdot>NID_i0_stm0_robot_ctrl,enter_i0_stm0_robot_ctrl,enter_move_stm0_robot_ctrl,share,terminate,internal__stm0_robot_ctrl\<cdot>NID_detect_stm0_robot_ctrl,internal__stm0_robot_ctrl\<cdot>NID_move_stm0_robot_ctrl,enter_stop_stm0_robot_ctrl,internal__stm0_robot_ctrl\<cdot>NID_stop_stm0_robot_ctrl \<rbrace> | \<rbrakk> 
  ((enter_i0_stm0_robot_ctrl \<rightarrow> Trans_stm0_robot_ctrl) [ share \<mapsto> share ]))" | 

"ncBehaviour_stm0_robot_ctrl = ((ncCoreBehaviour_stm0_robot_ctrl \<Zhide> \<lbrace> enter_i0_stm0_robot_ctrl,enter_detect_stm0_robot_ctrl,enter_stop_stm0_robot_ctrl,enter_move_stm0_robot_ctrl,enter_f0_stm0_robot_ctrl,exit_stm0_robot_ctrl,exited_stm0_robot_ctrl,internal__stm0_robot_ctrl \<rbrace>) [  ])" | 

"machineBody_stm0_robot_ctrl = ((ncBehaviour_stm0_robot_ctrl
  \<lbrakk> | \<lbrace> interrupt_stm0_robot_ctrl \<rbrace> | \<rbrakk> 
  Skip) \<Zhide> \<lbrace> enteredSS_stm0_robot_ctrl \<rbrace>)" | 

"Memory_pos_stm0_robot_ctrl(value :: nat) = (((get_pos_stm0_robot_ctrl\<^bold>!value \<rightarrow> Memory_pos_stm0_robot_ctrl(value))
  \<box>
  ((set_pos_stm0_robot_ctrl\<^bold>?x__ \<rightarrow> Memory_pos_stm0_robot_ctrl(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"varMemory_stm0_robot_ctrl = Memory_pos_stm0_robot_ctrl(0)" | 

"stateful_stm0_robot_ctrl = ((machineBody_stm0_robot_ctrl
  \<lbrakk> | \<lbrace> get_pos,set_pos,terminate \<rbrace> | \<rbrakk> 
  varMemory_stm0_robot_ctrl) \<Zhide> \<lbrace> get_pos,set_pos,terminate \<rbrace>)" | 

"sharedMemory_obs(value :: int) = (((get_obs\<^bold>!value \<rightarrow> sharedMemory_obs(value))
  \<box>
  ((set_obs\<^bold>?x__ \<rightarrow> sharedMemory_obs(x__))
  \<box>
  ((set_EXT_obs\<^bold>?x__ \<rightarrow> sharedMemory_obs(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedVarMemory_stm0_robot_ctrl = sharedMemory_obs(0)" | 

"stm_stm0_robot_ctrl = ((((((stateful_stm0_robot_ctrl \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [ share \<mapsto> set_EXT_obs ])
  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
  Skip)
  \<lbrakk> | \<lbrace> set_obs,set_EXT_obs,terminate,get_obs \<rbrace> | \<rbrakk> 
  sharedVarMemory_stm0_robot_ctrl) \<Zhide> \<lbrace> get_obs \<rbrace>)" | 

"composeMachines_robot_ctrl = (stm_stm0_robot_ctrl [ set_dest \<mapsto> set_dest ])" | 

"crtlMemory_robot_ctrl(obs :: int, dest :: nat) = (((set_obs\<^bold>?x__ \<rightarrow> ctrlMemory_robot_ctrl(x__,dest))
  \<box>
  (terminate \<rightarrow> Skip)))" | 

"controller_action_robot_ctrl = ((composeMachines_robot_ctrl
  \<lbrakk> | \<lbrace> set_obs,set_dest,terminate \<rbrace> | \<rbrakk> 
  crtlMemory_robot_ctrl(0,dest)) \<Zhide> \<lbrace> set_obs,set_dest \<rbrace>)"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess controller_action_robot_ctrl"

end




theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_move_C1_M = 
	NID_i0_move_C1_M | 
	NID_f0_move_C1_M	
	
datatype NIDS_stm0_C1_M = 
	NID_i0_stm0_C1_M | 
	NID_s0_stm0_C1_M | 
	NID_f0_stm0_C1_M	
	
datatype NIDS_stm1_C1_M = 
	NID_i0_stm1_C1_M | 
	NID_s0_stm1_C1_M | 
	NID_f0_stm1_C1_M



\<comment> \<open>constant and function declaration\<close>
consts angle :: "nat \<Rightarrow> nat"


\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
	
\<comment> \<open>event_channel_pltf_M\<close>

p1_in :: unit 
p1_out :: unit 
	
\<comment> \<open>undefined_op_channel_pltf_M\<close>

move2Call :: "real\<times>int"

move4Call :: unit 

move1Call :: "int"

move5Call :: "real\<times>int"
	
\<comment> \<open>var_channels_pltf_M\<close>

get_pv1 :: "int"
set_pv1 :: "int"

get_a1 :: "int\<times>int"
set_a1 :: "int\<times>int"

get_a3 :: "int"
set_a3 :: "int"

get_m :: "int"
set_m :: "int"
	
\<comment> \<open>var_channels_ctrl_C1_M\<close>

get_cv1 :: "int"
set_cv1 :: "int"

get_x :: "int"
set_x :: "int"
	
\<comment> \<open>shared_var_channel_ctrl_C1_M\<close>

set_EXT_m :: "int"

set_EXT_a1 :: "int\<times>int"

set_EXT_a3 :: "int"
	
\<comment> \<open>event_channel_ctrl_C1_M\<close>

evta_in :: "int"
evta_out :: "int"
	
\<comment> \<open>undefined_op_channel_ctrl_C1_M\<close>

move2Call :: "real\<times>int"

move4Call :: unit 

move5Call :: "real\<times>int"
	
\<comment> \<open>internal_channel_stmbd_move_C1_M\<close>

internal__move_C1_M :: "NIDS_move_C1_M"
	
\<comment> \<open>flowchannel_stmbd_move_C1_M\<close>

interrupt_move_C1_M :: unit 
exited_move_C1_M :: unit 
exit_move_C1_M :: unit 
	
\<comment> \<open>var_channel_stmbd_move_C1_M\<close>

get_mv_var1 :: "int"
set_mv_var1 :: "int"
setL_mv_var1 :: "int"
setR_mv_var1 :: "int"

get_mv_var2 :: "int"
set_mv_var2 :: "int"
setL_mv_var2 :: "int"
setR_mv_var2 :: "int"
	
\<comment> \<open>event_channel_stmbd_move_C1_M\<close>

mv_evt1_in :: "int"
mv_evt1_out :: "int"

mv_evt1__in :: "NIDS_move_C1_M\<times>int"
	
\<comment> \<open>junction_channel_in_stmbd_i0_move_C1_M\<close>

enter_i0_move_C1_M :: unit 
interrupt_i0_move_C1_M :: unit 
	
\<comment> \<open>state_channel_in_stmbd_f0_move_C1_M\<close>

enter_f0_move_C1_M :: unit 
entered_f0_move_C1_M :: unit 
interrupt_f0_move_C1_M :: unit 
enteredL_f0_move_C1_M :: unit 
enteredR_f0_move_C1_M :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm0_C1_M\<close>

internal__stm0_C1_M :: "NIDS_stm0_C1_M"
	
\<comment> \<open>flowchannel_stmbd_stm0_C1_M\<close>

interrupt_stm0_C1_M :: unit 
exited_stm0_C1_M :: unit 
exit_stm0_C1_M :: unit 
	
\<comment> \<open>var_channel_stmbd_stm0_C1_M\<close>

get_l :: "int"
set_l :: "int"
setL_l :: "int"
setR_l :: "int"

get_a :: "int"
set_a :: "int"
setL_a :: "int"
setR_a :: "int"
	
\<comment> \<open>shared_var_channel_stmbd_stm0_C1_M\<close>

set_EXT_m :: "int"

set_EXT_a1 :: "int\<times>int"

set_EXT_a3 :: "int"
	
\<comment> \<open>event_channel_stmbd_stm0_C1_M\<close>

mv_evt1_in :: "int"
mv_evt1_out :: "int"

stop_in :: unit 
stop_out :: unit 

event1_in :: "int\<times>int"
event1_out :: "int\<times>int"

event2_in :: "int"
event2_out :: "int"

trigger1_in :: "int"
trigger1_out :: "int"

mv_evt1__in :: "NIDS_stm0_C1_M\<times>int"

stop__in :: "NIDS_stm0_C1_M"

event1__in :: "NIDS_stm0_C1_M\<times>int\<times>int"

event2__in :: "NIDS_stm0_C1_M\<times>int"

trigger1__in :: "NIDS_stm0_C1_M\<times>int"
	
\<comment> \<open>undefined_op_channel_stmbd_stm0_C1_M\<close>

move2Call :: "real\<times>int"

move4Call :: unit 

moveCall :: "real\<times>int"

move5Call :: "real\<times>int"
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm0_C1_M\<close>

enter_i0_stm0_C1_M :: unit 
interrupt_i0_stm0_C1_M :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s0_stm0_C1_M\<close>

enter_s0_stm0_C1_M :: unit 
entered_s0_stm0_C1_M :: unit 
interrupt_s0_stm0_C1_M :: unit 
enteredL_s0_stm0_C1_M :: unit 
enteredR_s0_stm0_C1_M :: unit 
	
\<comment> \<open>state_channel_in_stmbd_f0_stm0_C1_M\<close>

enter_f0_stm0_C1_M :: unit 
entered_f0_stm0_C1_M :: unit 
interrupt_f0_stm0_C1_M :: unit 
enteredL_f0_stm0_C1_M :: unit 
enteredR_f0_stm0_C1_M :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm1_C1_M\<close>

internal__stm1_C1_M :: "NIDS_stm1_C1_M"
	
\<comment> \<open>flowchannel_stmbd_stm1_C1_M\<close>

interrupt_stm1_C1_M :: unit 
exited_stm1_C1_M :: unit 
exit_stm1_C1_M :: unit 
	
\<comment> \<open>var_channel_stmbd_stm1_C1_M\<close>

get_l :: "int"
set_l :: "int"
setL_l :: "int"
setR_l :: "int"

get_a :: "int"
set_a :: "int"
setL_a :: "int"
setR_a :: "int"
	
\<comment> \<open>shared_var_channel_stmbd_stm1_C1_M\<close>

set_EXT_m :: "int"

set_EXT_a1 :: "int\<times>int"

set_EXT_a3 :: "int"
	
\<comment> \<open>event_channel_stmbd_stm1_C1_M\<close>

mv_evt1_in :: "int"
mv_evt1_out :: "int"

stop_in :: unit 
stop_out :: unit 

event1_in :: "int\<times>int"
event1_out :: "int\<times>int"

event2_in :: "int"
event2_out :: "int"

trigger1_in :: "int"
trigger1_out :: "int"

mv_evt1__in :: "NIDS_stm1_C1_M\<times>int"

stop__in :: "NIDS_stm1_C1_M"

event1__in :: "NIDS_stm1_C1_M\<times>int\<times>int"

event2__in :: "NIDS_stm1_C1_M\<times>int"

trigger1__in :: "NIDS_stm1_C1_M\<times>int"
	
\<comment> \<open>undefined_op_channel_stmbd_stm1_C1_M\<close>

move2Call :: "real\<times>int"

move4Call :: unit 

moveCall :: "real\<times>int"

move5Call :: "real\<times>int"
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm1_C1_M\<close>

enter_i0_stm1_C1_M :: unit 
interrupt_i0_stm1_C1_M :: unit 
	
\<comment> \<open>state_channel_in_stmbd_s0_stm1_C1_M\<close>

enter_s0_stm1_C1_M :: unit 
entered_s0_stm1_C1_M :: unit 
interrupt_s0_stm1_C1_M :: unit 
enteredL_s0_stm1_C1_M :: unit 
enteredR_s0_stm1_C1_M :: unit 
	
\<comment> \<open>state_channel_in_stmbd_f0_stm1_C1_M\<close>

enter_f0_stm1_C1_M :: unit 
entered_f0_stm1_C1_M :: unit 
interrupt_f0_stm1_C1_M :: unit 
enteredL_f0_stm1_C1_M :: unit 
enteredR_f0_stm1_C1_M :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "shared_variable_events_ctrl_C1_M = \<lbrace> 
	  set_EXT_m, 
	  set_EXT_a1, 
	  set_EXT_a3 \<rbrace>"
	
definition "enterSS_in_stmbd_move_C1_M = \<lbrace> 
	  enter_i0_move_C1_M, 
	  enter_f0_move_C1_M \<rbrace>"
	
definition "enteredSS_in_stmbd_move_C1_M = \<lbrace> 
	  entered_f0_move_C1_M \<rbrace>"
	
definition "internal_events_in_stmbd_move_C1_M = \<lbrace> 
	  enter_i0_move_C1_M, 
	  enter_f0_move_C1_M, 
	  entered_f0_move_C1_M, 
	  interrupt_move_C1_M, 
	  exited_move_C1_M \<rbrace>"
	
definition "shared_variable_events_in_stmbd_move_C1_M = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_stm_move_C1_M = \<lbrace> 
	  terminate, 
	  mv_evt1_in, 
	  mv_evt1_out \<rbrace>"
	
definition "enterSS_in_stmbd_stm0_C1_M = \<lbrace> 
	  enter_i0_stm0_C1_M, 
	  enter_s0_stm0_C1_M, 
	  enter_f0_stm0_C1_M \<rbrace>"
	
definition "enteredSS_in_stmbd_stm0_C1_M = \<lbrace> 
	  entered_s0_stm0_C1_M, 
	  entered_f0_stm0_C1_M \<rbrace>"
	
definition "internal_events_in_stmbd_stm0_C1_M = \<lbrace> 
	  enter_i0_stm0_C1_M, 
	  enter_s0_stm0_C1_M, 
	  enter_f0_stm0_C1_M, 
	  entered_s0_stm0_C1_M, 
	  entered_f0_stm0_C1_M, 
	  interrupt_stm0_C1_M, 
	  exited_stm0_C1_M \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm0_C1_M = \<lbrace> 
	  set_EXT_m, 
	  set_EXT_a1, 
	  set_EXT_a3 \<rbrace>"
	
definition "sem__events_stm_stm0_C1_M = \<lbrace> 
	  terminate, 
	  set_EXT_m, 
	  set_EXT_a1, 
	  set_EXT_a3, 
	  mv_evt1_in, 
	  mv_evt1_out, 
	  stop_in, 
	  stop_out, 
	  event1_in, 
	  event1_out, 
	  event2_in, 
	  event2_out, 
	  trigger1_in, 
	  trigger1_out, 
	  move2Call, 
	  move4Call, 
	  moveCall, 
	  move5Call \<rbrace>"
	
definition "enterSS_in_stmbd_stm1_C1_M = \<lbrace> 
	  enter_i0_stm1_C1_M, 
	  enter_s0_stm1_C1_M, 
	  enter_f0_stm1_C1_M \<rbrace>"
	
definition "enteredSS_in_stmbd_stm1_C1_M = \<lbrace> 
	  entered_f0_stm1_C1_M, 
	  entered_s0_stm1_C1_M \<rbrace>"
	
definition "internal_events_in_stmbd_stm1_C1_M = \<lbrace> 
	  enter_i0_stm1_C1_M, 
	  enter_s0_stm1_C1_M, 
	  enter_f0_stm1_C1_M, 
	  entered_f0_stm1_C1_M, 
	  entered_s0_stm1_C1_M, 
	  interrupt_stm1_C1_M, 
	  exited_stm1_C1_M \<rbrace>"
	
definition "shared_variable_events_in_stmbd_stm1_C1_M = \<lbrace> 
	  set_EXT_m, 
	  set_EXT_a1, 
	  set_EXT_a3 \<rbrace>"
	
definition "sem__events_stm_stm1_C1_M = \<lbrace> 
	  terminate, 
	  set_EXT_m, 
	  set_EXT_a1, 
	  set_EXT_a3, 
	  mv_evt1_in, 
	  mv_evt1_out, 
	  stop_in, 
	  stop_out, 
	  event1_in, 
	  event1_out, 
	  event2_in, 
	  event2_out, 
	  trigger1_in, 
	  trigger1_out, 
	  move2Call, 
	  move4Call, 
	  moveCall, 
	  move5Call \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
	"relu x = max 0 x"


locale controller_proc_C1_M
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"Inactive_i0_move_C1_M = (SSTOP \<triangle> (Activation_i0_move_C1_M
  \<box>
  Termination_i0_move_C1_M))" | 

"Activation_i0_move_C1_M = (enter_i0_move_C1_M \<rightarrow> Active_i0_move_C1_M)" | 

"Termination_i0_move_C1_M = (terminate \<rightarrow> Skip)" | 

"Active_i0_move_C1_M = ((SSTOP \<triangle> (interrupt_i0_move_C1_M \<rightarrow> Skip));; Inactive_i0_move_C1_M)" | 

"Inactive_f0_move_C1_M = (SSTOP \<triangle> (Activation_f0_move_C1_M
  \<box>
  Termination_f0_move_C1_M))" | 

"Activation_f0_move_C1_M = (enter_f0_move_C1_M \<rightarrow> Entering_f0_move_C1_M)" | 

"Termination_f0_move_C1_M = (terminate \<rightarrow> Skip)" | 

"Entering_f0_move_C1_M = (entered_f0_move_C1_M \<rightarrow> Active_f0_move_C1_M)" | 

"Active_f0_move_C1_M = (SSTOP \<triangle> (Termination_f0_move_C1_M
  \<box>
  (interrupt_f0_move_C1_M \<rightarrow> Interrupted_f0_move_C1_M)))" | 

"Interrupted_f0_move_C1_M = (SSTOP \<triangle> (exit_move_C1_M \<rightarrow> (exited_move_C1_M \<rightarrow> Inactivef0_move_C1_M)))" | 

"composeNodes_move_C1_M = (Inactive_f0_move_C1_M
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_i0_move_C1_M)" | 

"Trans_move_C1_M = (((((internal__move_C1_M\<^bold>.NID_i0_move_C1_M \<rightarrow> ((SSTOP \<triangle> (mv_evt1_out\<^bold>!3 \<rightarrow> Skip));; CALL__move1(2)));; (enter_f0_move_C1_M \<rightarrow> Skip))
  \<box>
  (share \<rightarrow> Skip));; Trans_move_C1_M)
  \<box>
  (((interrupt_move_C1_M \<rightarrow> (SSTOP \<triangle> (exit_move_C1_M \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_move_C1_M \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip)))" | 

"ncCoreBehaviour_move_C1_M = (((composeNodes_move_C1_M [ interrupt_i0_move_C1_M \<mapsto> internal__move_C1_M\<cdot>NID_i0_move_C1_M,  
 interrupt_f0_move_C1_M \<mapsto> interrupt_move_C1_M ]) [ share \<mapsto> share ])
  \<lbrakk> | \<lbrace> enter_f0_move_C1_M,internal__move_C1_M\<cdot>NID_i0_move_C1_M,enter_i0_move_C1_M,exited_move_C1_M,interrupt_move_C1_M,share,exit_move_C1_M,terminate \<rbrace> | \<rbrakk> 
  ((enter_i0_move_C1_M \<rightarrow> Trans_move_C1_M) [ share \<mapsto> share ]))" | 

"ncBehaviour_move_C1_M = ((ncCoreBehaviour_move_C1_M \<Zhide> \<lbrace> enter_i0_move_C1_M,enter_f0_move_C1_M,exit_move_C1_M,exited_move_C1_M,internal__move_C1_M \<rbrace>) [  ])" | 

"machineBody_move_C1_M = ((ncBehaviour_move_C1_M
  \<lbrakk> | \<lbrace> interrupt_move_C1_M \<rbrace> | \<rbrakk> 
  Skip) \<Zhide> \<lbrace> enteredSS_move_C1_M \<rbrace>)" | 

"Memory_mv_var2_move_C1_M(value :: int) = (((get_mv_var2_move_C1_M\<^bold>!value \<rightarrow> Memory_mv_var2_move_C1_M(value))
  \<box>
  ((set_mv_var2_move_C1_M\<^bold>?x__ \<rightarrow> Memory_mv_var2_move_C1_M(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"Memory_mv_var1_move_C1_M(value :: int) = (((get_mv_var1_move_C1_M\<^bold>!value \<rightarrow> Memory_mv_var1_move_C1_M(value))
  \<box>
  ((set_mv_var1_move_C1_M\<^bold>?x__ \<rightarrow> Memory_mv_var1_move_C1_M(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"varMemory_move_C1_M = (Memory_mv_var2_move_C1_M(0)
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  Memory_mv_var1_move_C1_M(0))" | 

"stm_op_move_C1_M = (((machineBody_move_C1_M
  \<lbrakk> | \<lbrace> get_mv_var1,set_mv_var2,terminate,get_mv_var2,set_mv_var1 \<rbrace> | \<rbrakk> 
  varMemory_move_C1_M) \<Zhide> \<lbrace> get_mv_var1,set_mv_var2,terminate,get_mv_var2,set_mv_var1 \<rbrace>) \<Zhide> \<lbrace> terminate \<rbrace>)" | 

"move2Call(lv :: real, a :: int) = ((move2Call\<^bold>.param_lv\<^bold>.param_a \<rightarrow> Skip))" | 

"move5Call(lv :: real, a :: int) = ((move5Call\<^bold>.param_lv\<^bold>.param_a \<rightarrow> Skip))" | 

"move4Call = (move4Call \<rightarrow> Skip)" | 

"Inactive_i0_stm0_C1_M = (SSTOP \<triangle> (Activation_i0_stm0_C1_M
  \<box>
  Termination_i0_stm0_C1_M))" | 

"Activation_i0_stm0_C1_M = (enter_i0_stm0_C1_M \<rightarrow> Active_i0_stm0_C1_M)" | 

"Termination_i0_stm0_C1_M = (terminate \<rightarrow> Skip)" | 

"Active_i0_stm0_C1_M = ((SSTOP \<triangle> (interrupt_i0_stm0_C1_M \<rightarrow> Skip));; Inactive_i0_stm0_C1_M)" | 

"Inactive_s0_stm0_C1_M = (SSTOP \<triangle> (Activation_s0_stm0_C1_M
  \<box>
  Termination_s0_stm0_C1_M))" | 

"Activation_s0_stm0_C1_M = (enter_s0_stm0_C1_M \<rightarrow> Active_s0_stm0_C1_M)" | 

"Termination_s0_stm0_C1_M = (terminate \<rightarrow> Skip)" | 

"Active_s0_stm0_C1_M = (((SSTOP \<triangle> (set_a\<^bold>!3 \<rightarrow> Skip));; (CALL__move4();; ((SSTOP \<triangle> (event1_in\<^bold>?a1 \<rightarrow> (SSTOP \<triangle> (set_a1\<^bold>!a1 \<rightarrow> Skip))));; ((SSTOP \<triangle> (event2_in\<^bold>?a3 \<rightarrow> (SSTOP \<triangle> (set_a3\<^bold>!a3 \<rightarrow> Skip))));; (SSTOP \<triangle> (get_m\<^bold>?m \<rightarrow> (SSTOP \<triangle> (set_m\<^bold>!(m + c1) \<rightarrow> Skip))))))));; (Behaviour_s0_stm0_C1_M;; Exiting_s0_stm0_C1_M))" | 

"Behaviour_s0_stm0_C1_M = (entered_s0_stm0_C1_M \<rightarrow> During_s0_stm0_C1_M)" | 

"During_s0_stm0_C1_M = ((((SSTOP \<triangle> (get_a3\<^bold>?a3 \<rightarrow> (SSTOP \<triangle> (get_l\<^bold>?l \<rightarrow> (SSTOP \<triangle> (set_a\<^bold>!((a3 + l) + 1) \<rightarrow> Skip))))));; CALL__move2(4,5));; SSTOP) \<triangle> (interrupt_s0_stm0_C1_M \<rightarrow> Skip))" | 

"Exiting_s0_stm0_C1_M = ((SSTOP \<triangle> (exit_stm0_C1_M \<rightarrow> Skip));; ((CALL__move1(5);; CALL__move(1,2));; (exited_stm0_C1_M \<rightarrow> Inactive_s0_stm0_C1_M)))" | 

"Inactive_f0_stm0_C1_M = (SSTOP \<triangle> (Activation_f0_stm0_C1_M
  \<box>
  Termination_f0_stm0_C1_M))" | 

"Activation_f0_stm0_C1_M = (enter_f0_stm0_C1_M \<rightarrow> Entering_f0_stm0_C1_M)" | 

"Termination_f0_stm0_C1_M = (terminate \<rightarrow> Skip)" | 

"Entering_f0_stm0_C1_M = (entered_f0_stm0_C1_M \<rightarrow> Active_f0_stm0_C1_M)" | 

"Active_f0_stm0_C1_M = (SSTOP \<triangle> (Termination_f0_stm0_C1_M
  \<box>
  (interrupt_f0_stm0_C1_M \<rightarrow> Interrupted_f0_stm0_C1_M)))" | 

"Interrupted_f0_stm0_C1_M = (SSTOP \<triangle> (exit_stm0_C1_M \<rightarrow> (exited_stm0_C1_M \<rightarrow> Inactivef0_stm0_C1_M)))" | 

"composeNodes_stm0_C1_M = ((Inactive_i0_stm0_C1_M
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_s0_stm0_C1_M)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_f0_stm0_C1_M)" | 

"Trans_stm0_C1_M = (SSTOP \<triangle> (get_a3\<^bold>?a3 \<rightarrow> (((((((internal__stm0_C1_M\<^bold>.NID_i0_stm0_C1_M \<rightarrow> Skip);; (enter_s0_stm0_C1_M \<rightarrow> Skip))
  \<box>
  ((stop__in\<^bold>.NID_s0_stm0_C1_M \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_C1_M \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_C1_M \<rightarrow> Skip);; (enter_f0_stm0_C1_M \<rightarrow> Skip))))))
  \<box>
  ((a3 > 4) \<^bold>& (((event2__in\<^bold>.NID_s0_stm0_C1_M\<^bold>?a \<rightarrow> (SSTOP \<triangle> (set_a\<^bold>!a \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_stm0_C1_M \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_C1_M \<rightarrow> (SSTOP \<triangle> (get_a3\<^bold>?a3 \<rightarrow> (SSTOP \<triangle> (trigger1_out\<^bold>!((a3 + c2) + c3) \<rightarrow> Skip)))));; (enter_s0_stm0_C1_M \<rightarrow> Skip))))))))
  \<box>
  (share \<rightarrow> Skip));; Trans_stm0_C1_M)
  \<box>
  (((interrupt_stm0_C1_M \<rightarrow> (SSTOP \<triangle> (exit_stm0_C1_M \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0_C1_M \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"ncCoreBehaviour_stm0_C1_M = ((((composeNodes_stm0_C1_M [ interrupt_i0_stm0_C1_M \<mapsto> internal__stm0_C1_M\<cdot>NID_i0_stm0_C1_M,  
 interrupt_s0_stm0_C1_M \<mapsto> stop__in\<cdot>NID_s0_stm0_C1_M,  
 interrupt_s0_stm0_C1_M \<mapsto> event2__in\<cdot>NID_s0_stm0_C1_M,  
 interrupt_s0_stm0_C1_M \<mapsto> interrupt_stm0_C1_M,  
 interrupt_f0_stm0_C1_M \<mapsto> interrupt_stm0_C1_M ]) [ share \<mapsto> share,  
 set_a3 \<mapsto> setL_a3 ])
  \<lbrakk> | \<lbrace> interrupt_stm0_C1_M,enter_i0_stm0_C1_M,event2__in\<cdot>NID_s0_stm0_C1_M,enter_s0_stm0_C1_M,share,enter_f0_stm0_C1_M,terminate,setL_a3,exit_stm0_C1_M,stop__in\<cdot>NID_s0_stm0_C1_M,internal__stm0_C1_M\<cdot>NID_i0_stm0_C1_M,exited_stm0_C1_M \<rbrace> | \<rbrakk> 
  ((enter_i0_stm0_C1_M \<rightarrow> Trans_stm0_C1_M) [ share \<mapsto> share,  
 share \<mapsto> setL_a3 ])) [ setL_a3 \<mapsto> set_a3 ])" | 

"ncBehaviour_stm0_C1_M = ((ncCoreBehaviour_stm0_C1_M \<Zhide> \<lbrace> enter_i0_stm0_C1_M,enter_s0_stm0_C1_M,enter_f0_stm0_C1_M,exit_stm0_C1_M,exited_stm0_C1_M,internal__stm0_C1_M \<rbrace>) [ stop__in\<cdot>x \<mapsto> stop_in,  
 event2__in\<cdot>x \<mapsto> event2_in ])" | 

"machineBody_stm0_C1_M = ((ncBehaviour_stm0_C1_M
  \<lbrakk> | \<lbrace> interrupt_stm0_C1_M \<rbrace> | \<rbrakk> 
  Skip) \<Zhide> \<lbrace> enteredSS_stm0_C1_M \<rbrace>)" | 

"Memory_l_stm0_C1_M(value :: int) = (((get_l_stm0_C1_M\<^bold>!value \<rightarrow> Memory_l_stm0_C1_M(value))
  \<box>
  ((set_l_stm0_C1_M\<^bold>?x__ \<rightarrow> Memory_l_stm0_C1_M(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"Memory_a_stm0_C1_M(value :: int) = (((get_a_stm0_C1_M\<^bold>!value \<rightarrow> Memory_a_stm0_C1_M(value))
  \<box>
  ((set_a_stm0_C1_M\<^bold>?x__ \<rightarrow> Memory_a_stm0_C1_M(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"varMemory_stm0_C1_M = (Memory_l_stm0_C1_M(c6)
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  Memory_a_stm0_C1_M(0))" | 

"stateful_stm0_C1_M = ((machineBody_stm0_C1_M
  \<lbrakk> | \<lbrace> set_a,get_a,get_l,set_l,terminate \<rbrace> | \<rbrakk> 
  varMemory_stm0_C1_M) \<Zhide> \<lbrace> set_a,get_a,get_l,set_l,terminate \<rbrace>)" | 

"sharedMemory_a3(value :: int) = (((get_a3\<^bold>!value \<rightarrow> sharedMemory_a3(value))
  \<box>
  ((set_a3\<^bold>?x__ \<rightarrow> sharedMemory_a3(x__))
  \<box>
  ((set_EXT_a3\<^bold>?x__ \<rightarrow> sharedMemory_a3(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedMemory_m(value :: int) = (((get_m\<^bold>!value \<rightarrow> sharedMemory_m(value))
  \<box>
  ((set_m\<^bold>?x__ \<rightarrow> sharedMemory_m(x__))
  \<box>
  ((set_EXT_m\<^bold>?x__ \<rightarrow> sharedMemory_m(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedMemory_a1(value :: int\<times>int) = (((get_a1\<^bold>!value \<rightarrow> sharedMemory_a1(value))
  \<box>
  ((set_a1\<^bold>?x__ \<rightarrow> sharedMemory_a1(x__))
  \<box>
  ((set_EXT_a1\<^bold>?x__ \<rightarrow> sharedMemory_a1(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedVarMemory_stm0_C1_M = ((sharedMemory_a3(0)
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  sharedMemory_m(0))
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  sharedMemory_a1(0,0))" | 

"stm_stm0_C1_M = ((((((stateful_stm0_C1_M \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [ share \<mapsto> set_EXT_a3,  
 share \<mapsto> set_EXT_m,  
 share \<mapsto> set_EXT_a1 ])
  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
  Skip)
  \<lbrakk> | \<lbrace> get_a1,get_a3,set_m,set_EXT_a3,set_EXT_m,terminate,set_a3,get_m,set_a1,set_EXT_a1 \<rbrace> | \<rbrakk> 
  sharedVarMemory_stm0_C1_M) \<Zhide> \<lbrace> get_a1,get_a3,get_m \<rbrace>)" | 

"Inactive_i0_stm1_C1_M = (SSTOP \<triangle> (Activation_i0_stm1_C1_M
  \<box>
  Termination_i0_stm1_C1_M))" | 

"Activation_i0_stm1_C1_M = (enter_i0_stm1_C1_M \<rightarrow> Active_i0_stm1_C1_M)" | 

"Termination_i0_stm1_C1_M = (terminate \<rightarrow> Skip)" | 

"Active_i0_stm1_C1_M = ((SSTOP \<triangle> (interrupt_i0_stm1_C1_M \<rightarrow> Skip));; Inactive_i0_stm1_C1_M)" | 

"Inactive_s0_stm1_C1_M = (SSTOP \<triangle> (Activation_s0_stm1_C1_M
  \<box>
  Termination_s0_stm1_C1_M))" | 

"Activation_s0_stm1_C1_M = (enter_s0_stm1_C1_M \<rightarrow> Active_s0_stm1_C1_M)" | 

"Termination_s0_stm1_C1_M = (terminate \<rightarrow> Skip)" | 

"Active_s0_stm1_C1_M = (((SSTOP \<triangle> (set_a\<^bold>!3 \<rightarrow> Skip));; (CALL__move4();; ((SSTOP \<triangle> (event1_in\<^bold>?a1 \<rightarrow> (SSTOP \<triangle> (set_a1\<^bold>!a1 \<rightarrow> Skip))));; ((SSTOP \<triangle> (event2_in\<^bold>?a3 \<rightarrow> (SSTOP \<triangle> (set_a3\<^bold>!a3 \<rightarrow> Skip))));; (SSTOP \<triangle> (get_m\<^bold>?m \<rightarrow> (SSTOP \<triangle> (set_m\<^bold>!(m + c1) \<rightarrow> Skip))))))));; (Behaviour_s0_stm1_C1_M;; Exiting_s0_stm1_C1_M))" | 

"Behaviour_s0_stm1_C1_M = (entered_s0_stm1_C1_M \<rightarrow> During_s0_stm1_C1_M)" | 

"During_s0_stm1_C1_M = ((((SSTOP \<triangle> (get_a3\<^bold>?a3 \<rightarrow> (SSTOP \<triangle> (get_l\<^bold>?l \<rightarrow> (SSTOP \<triangle> (set_a\<^bold>!((a3 + l) + 1) \<rightarrow> Skip))))));; CALL__move2(4,5));; SSTOP) \<triangle> (interrupt_s0_stm1_C1_M \<rightarrow> Skip))" | 

"Exiting_s0_stm1_C1_M = ((SSTOP \<triangle> (exit_stm1_C1_M \<rightarrow> Skip));; ((CALL__move1(5);; CALL__move(1,2));; (exited_stm1_C1_M \<rightarrow> Inactive_s0_stm1_C1_M)))" | 

"Inactive_f0_stm1_C1_M = (SSTOP \<triangle> (Activation_f0_stm1_C1_M
  \<box>
  Termination_f0_stm1_C1_M))" | 

"Activation_f0_stm1_C1_M = (enter_f0_stm1_C1_M \<rightarrow> Entering_f0_stm1_C1_M)" | 

"Termination_f0_stm1_C1_M = (terminate \<rightarrow> Skip)" | 

"Entering_f0_stm1_C1_M = (entered_f0_stm1_C1_M \<rightarrow> Active_f0_stm1_C1_M)" | 

"Active_f0_stm1_C1_M = (SSTOP \<triangle> (Termination_f0_stm1_C1_M
  \<box>
  (interrupt_f0_stm1_C1_M \<rightarrow> Interrupted_f0_stm1_C1_M)))" | 

"Interrupted_f0_stm1_C1_M = (SSTOP \<triangle> (exit_stm1_C1_M \<rightarrow> (exited_stm1_C1_M \<rightarrow> Inactivef0_stm1_C1_M)))" | 

"composeNodes_stm1_C1_M = ((Inactive_f0_stm1_C1_M
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_i0_stm1_C1_M)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_s0_stm1_C1_M)" | 

"Trans_stm1_C1_M = (SSTOP \<triangle> (get_a3\<^bold>?a3 \<rightarrow> (((((((internal__stm1_C1_M\<^bold>.NID_i0_stm1_C1_M \<rightarrow> Skip);; (enter_s0_stm1_C1_M \<rightarrow> Skip))
  \<box>
  ((stop__in\<^bold>.NID_s0_stm1_C1_M \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm1_C1_M \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm1_C1_M \<rightarrow> Skip);; (enter_f0_stm1_C1_M \<rightarrow> Skip))))))
  \<box>
  ((a3 > 4) \<^bold>& (((event2__in\<^bold>.NID_s0_stm1_C1_M\<^bold>?a \<rightarrow> (SSTOP \<triangle> (set_a\<^bold>!a \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_stm1_C1_M \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm1_C1_M \<rightarrow> (SSTOP \<triangle> (get_a3\<^bold>?a3 \<rightarrow> (SSTOP \<triangle> (trigger1_out\<^bold>!((a3 + c2) + c3) \<rightarrow> Skip)))));; (enter_s0_stm1_C1_M \<rightarrow> Skip))))))))
  \<box>
  (share \<rightarrow> Skip));; Trans_stm1_C1_M)
  \<box>
  (((interrupt_stm1_C1_M \<rightarrow> (SSTOP \<triangle> (exit_stm1_C1_M \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm1_C1_M \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"ncCoreBehaviour_stm1_C1_M = ((((composeNodes_stm1_C1_M [ interrupt_i0_stm1_C1_M \<mapsto> internal__stm1_C1_M\<cdot>NID_i0_stm1_C1_M,  
 interrupt_s0_stm1_C1_M \<mapsto> stop__in\<cdot>NID_s0_stm1_C1_M,  
 interrupt_s0_stm1_C1_M \<mapsto> event2__in\<cdot>NID_s0_stm1_C1_M,  
 interrupt_f0_stm1_C1_M \<mapsto> interrupt_stm1_C1_M,  
 interrupt_s0_stm1_C1_M \<mapsto> interrupt_stm1_C1_M ]) [ share \<mapsto> share,  
 set_a3 \<mapsto> setL_a3 ])
  \<lbrakk> | \<lbrace> internal__stm1_C1_M\<cdot>NID_i0_stm1_C1_M,enter_s0_stm1_C1_M,enter_i0_stm1_C1_M,exit_stm1_C1_M,exited_stm1_C1_M,interrupt_stm1_C1_M,share,terminate,setL_a3,event2__in\<cdot>NID_s0_stm1_C1_M,stop__in\<cdot>NID_s0_stm1_C1_M,enter_f0_stm1_C1_M \<rbrace> | \<rbrakk> 
  ((enter_i0_stm1_C1_M \<rightarrow> Trans_stm1_C1_M) [ share \<mapsto> share,  
 share \<mapsto> setL_a3 ])) [ setL_a3 \<mapsto> set_a3 ])" | 

"ncBehaviour_stm1_C1_M = ((ncCoreBehaviour_stm1_C1_M \<Zhide> \<lbrace> enter_i0_stm1_C1_M,enter_s0_stm1_C1_M,enter_f0_stm1_C1_M,exit_stm1_C1_M,exited_stm1_C1_M,internal__stm1_C1_M \<rbrace>) [ stop__in\<cdot>x \<mapsto> stop_in,  
 event2__in\<cdot>x \<mapsto> event2_in ])" | 

"machineBody_stm1_C1_M = ((ncBehaviour_stm1_C1_M
  \<lbrakk> | \<lbrace> interrupt_stm1_C1_M \<rbrace> | \<rbrakk> 
  Skip) \<Zhide> \<lbrace> enteredSS_stm1_C1_M \<rbrace>)" | 

"Memory_a_stm1_C1_M(value :: int) = (((get_a_stm1_C1_M\<^bold>!value \<rightarrow> Memory_a_stm1_C1_M(value))
  \<box>
  ((set_a_stm1_C1_M\<^bold>?x__ \<rightarrow> Memory_a_stm1_C1_M(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"Memory_l_stm1_C1_M(value :: int) = (((get_l_stm1_C1_M\<^bold>!value \<rightarrow> Memory_l_stm1_C1_M(value))
  \<box>
  ((set_l_stm1_C1_M\<^bold>?x__ \<rightarrow> Memory_l_stm1_C1_M(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"varMemory_stm1_C1_M = (Memory_a_stm1_C1_M(0)
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  Memory_l_stm1_C1_M(c6))" | 

"stateful_stm1_C1_M = ((machineBody_stm1_C1_M
  \<lbrakk> | \<lbrace> set_a,get_a,get_l,set_l,terminate \<rbrace> | \<rbrakk> 
  varMemory_stm1_C1_M) \<Zhide> \<lbrace> set_a,get_a,get_l,set_l,terminate \<rbrace>)" | 

"sharedMemory_a3(value :: int) = (((get_a3\<^bold>!value \<rightarrow> sharedMemory_a3(value))
  \<box>
  ((set_a3\<^bold>?x__ \<rightarrow> sharedMemory_a3(x__))
  \<box>
  ((set_EXT_a3\<^bold>?x__ \<rightarrow> sharedMemory_a3(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedMemory_m(value :: int) = (((get_m\<^bold>!value \<rightarrow> sharedMemory_m(value))
  \<box>
  ((set_m\<^bold>?x__ \<rightarrow> sharedMemory_m(x__))
  \<box>
  ((set_EXT_m\<^bold>?x__ \<rightarrow> sharedMemory_m(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedMemory_a1(value :: int\<times>int) = (((get_a1\<^bold>!value \<rightarrow> sharedMemory_a1(value))
  \<box>
  ((set_a1\<^bold>?x__ \<rightarrow> sharedMemory_a1(x__))
  \<box>
  ((set_EXT_a1\<^bold>?x__ \<rightarrow> sharedMemory_a1(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedVarMemory_stm1_C1_M = ((sharedMemory_a3(0)
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  sharedMemory_m(0))
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  sharedMemory_a1(0,0))" | 

"stm_stm1_C1_M = ((((((stateful_stm1_C1_M \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [ share \<mapsto> set_EXT_a3,  
 share \<mapsto> set_EXT_m,  
 share \<mapsto> set_EXT_a1 ])
  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
  Skip)
  \<lbrakk> | \<lbrace> get_a1,get_a3,set_m,set_EXT_a3,set_EXT_m,terminate,set_a3,get_m,set_a1,set_EXT_a1 \<rbrace> | \<rbrakk> 
  sharedVarMemory_stm1_C1_M) \<Zhide> \<lbrace> get_a1,get_a3,get_m \<rbrace>)" | 

"composeMachines_C1_M = ((stm_stm0_C1_M [ set_c3 \<mapsto> set_c3,  
 set_c2 \<mapsto> set_c2 ])
  \<lbrakk> | \<lbrace> terminate,set_c2,set_c3 \<rbrace> | \<rbrakk> 
  (stm_stm1_C1_M [ set_c3 \<mapsto> set_c3,  
 set_c2 \<mapsto> set_c2 ]))" | 

"crtlMemory_C1_M(a3 :: int, m :: int, a1 :: int\<times>int, cv1 :: int, c3 :: int, c2 :: int) = ((((set_cv1\<^bold>?x__ \<rightarrow> ctrlMemory_C1_M(a3,m,a1,x__,c3,c2))
  \<box>
  ((((set_Ext_a3\<^bold>?x__ \<rightarrow> (set_Ext_a3_stm1_C1_M\<^bold>!x__ \<rightarrow> (set_Ext_a3_stm0_C1_M\<^bold>!x__ \<rightarrow> Skip)));; ctrlMemory_C1_M(x__,m,a1,cv1,c3,c2))
  \<box>
  ((set_Ext_m\<^bold>?x__ \<rightarrow> (set_Ext_m_stm1_C1_M\<^bold>!x__ \<rightarrow> (set_Ext_m_stm0_C1_M\<^bold>!x__ \<rightarrow> Skip)));; ctrlMemory_C1_M(a3,x__,a1,cv1,c3,c2)))
  \<box>
  ((set_Ext_a1\<^bold>?x__ \<rightarrow> (set_Ext_a1_stm1_C1_M\<^bold>!x__ \<rightarrow> (set_Ext_a1_stm0_C1_M\<^bold>!x__ \<rightarrow> Skip)));; ctrlMemory_C1_M(a3,m,x__,cv1,c3,c2))))
  \<box>
  (terminate \<rightarrow> Skip)))" | 

"controller_action_C1_M = ((composeMachines_C1_M
  \<lbrakk> | \<lbrace> set_cv1,set_EXT_a3,set_EXT_m,terminate,set_c2,set_EXT_a1,set_c3 \<rbrace> | \<rbrakk> 
  crtlMemory_C1_M(0,0,0,0,0,c3,c2)) \<Zhide> \<lbrace> set_cv1,set_EXT_a3,set_EXT_m,set_EXT_a1 \<rbrace>)"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess controller_action_C1_M"

end

locale composeControllers_M
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

" composeControllers_M = 
	(controller_proc_C1_M
	  [ set_c3 \<mapsto> set_c3_M,  
	 set_c2 \<mapsto> set_c2_M ]) "

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess composeControllers_M.ProcDef"

end

locale modMemory_M
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"modMemory_action_M(a3 :: int, m :: int, a1 :: int\<times>int, pv1 :: int, c3 :: int, c2 :: int) = (((((((set_a3\<^bold>?x__ \<rightarrow> (set_Ext_a3_C1_M\<^bold>!x__ \<rightarrow> Skip));; modMemory_M(x__,m,a1,pv1,c3,c2))
  \<box>
  ((set_m\<^bold>?x__ \<rightarrow> (set_Ext_m_C1_M\<^bold>!x__ \<rightarrow> Skip));; modMemory_M(a3,x__,a1,pv1,c3,c2)))
  \<box>
  ((set_a1\<^bold>?x__ \<rightarrow> (set_Ext_a1_C1_M\<^bold>!x__ \<rightarrow> Skip));; modMemory_M(a3,m,x__,pv1,c3,c2)))
  \<box>
  (set_pv1\<^bold>?x__ \<rightarrow> modMemory_M(a3,m,a1,x__,c3,c2)))
  \<box>
  (terminate \<rightarrow> Skip)))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess modMemory_action_M"

end

locale RCModule_M
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

" RCModule_M = 
	((modMemory_M \<lbrakk> | \<lbrace> set_m,set_EXT_a3,set_pv1,set_EXT_m,set_a3,set_c2,set_a1,set_c3,set_EXT_a1 \<rbrace> | \<rbrakk> composeControllers_M) \<Zhide> \<lbrace> set_m,set_EXT_a3,set_pv1,set_EXT_m,set_a3,set_c2,set_a1,set_c3,set_EXT_a1,terminate \<rbrace>) "

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess RCModule_M.ProcDef"

end
 
end






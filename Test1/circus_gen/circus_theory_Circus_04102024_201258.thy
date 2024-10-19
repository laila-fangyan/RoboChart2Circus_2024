theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm0_C1_M_pkg0 = 
	NID_i0_stm0_C1_M_pkg0 | 
	NID_s0_stm0_C1_M_pkg0 | 
	NID_f0_stm0_C1_M_pkg0



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>internal_channel_stm0_C1_M_pkg0\<close>

internal__stm0_C1_M_pkg0 :: "NIDS_stm0_C1_M_pkg0"
	
\<comment> \<open>flowchannel_stm0_C1_M_pkg0\<close>

interrupt_stm0_C1_M_pkg0 :: unit 
exited_stm0_C1_M_pkg0 :: unit 
exit_stm0_C1_M_pkg0 :: unit 
terminate :: unit 
	
\<comment> \<open>variable_channel_stm0_C1_M_pkg0\<close>

get_l :: "int"
set_l :: "int"
setL_l :: "int"
setR_l :: "int"

get_a :: "int"
set_a :: "int"
setL_a :: "int"
setR_a :: "int"
	
\<comment> \<open>shared_var_channel_stm0_C1_M_pkg0\<close>

set_EXT_m :: "int"

set_EXT_a3 :: "int"

set_EXT_a1 :: "int\<times>int"
	
\<comment> \<open>event_channel_stm0_C1_M_pkg0\<close>

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

mv_evt1__in :: "NIDS_stm0_C1_M_pkg0\<times>int"

stop__in :: "NIDS_stm0_C1_M_pkg0"

event1__in :: "NIDS_stm0_C1_M_pkg0\<times>int\<times>int"

event2__in :: "NIDS_stm0_C1_M_pkg0\<times>int"

trigger1__in :: "NIDS_stm0_C1_M_pkg0\<times>int"
	
\<comment> \<open>undefined_op_channel_stm0_C1_M_pkg0\<close>

move2Call :: "real\<times>int"

move4Call :: unit 

moveCall :: "real\<times>int"

move5Call :: "real\<times>int"
	
\<comment> \<open>junction_channel_i0_stm0_C1_M_pkg0\<close>

enter_i0_stm0_C1_M_pkg0 :: unit 
interrupt_i0_stm0_C1_M_pkg0 :: unit 
	
\<comment> \<open>state_channel_s0_stm0_C1_M_pkg0\<close>

enter_s0_stm0_C1_M_pkg0 :: unit 
entered_s0_stm0_C1_M_pkg0 :: unit 
interrupt_s0_stm0_C1_M_pkg0 :: unit 
enteredL_s0_stm0_C1_M_pkg0 :: unit 
enteredR_s0_stm0_C1_M_pkg0 :: unit 
	
\<comment> \<open>state_channel_f0_stm0_C1_M_pkg0\<close>

enter_f0_stm0_C1_M_pkg0 :: unit 
entered_f0_stm0_C1_M_pkg0 :: unit 
interrupt_f0_stm0_C1_M_pkg0 :: unit 
enteredL_f0_stm0_C1_M_pkg0 :: unit 
enteredR_f0_stm0_C1_M_pkg0 :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_stm0_C1_M_pkg0 = \<lbrace> 
	  enter_i0_stm0_C1_M_pkg0, 
	  enter_s0_stm0_C1_M_pkg0, 
	  enter_f0_stm0_C1_M_pkg0 \<rbrace>"
	
definition "enteredSS_stm0_C1_M_pkg0 = \<lbrace> 
	  entered_f0_stm0_C1_M_pkg0, 
	  entered_s0_stm0_C1_M_pkg0 \<rbrace>"
	
definition "internal_events_stm0_C1_M_pkg0 = \<lbrace> 
	  enter_i0_stm0_C1_M_pkg0, 
	  enter_s0_stm0_C1_M_pkg0, 
	  enter_f0_stm0_C1_M_pkg0, 
	  entered_f0_stm0_C1_M_pkg0, 
	  entered_s0_stm0_C1_M_pkg0, 
	  interrupt_stm0_C1_M_pkg0, 
	  exited_stm0_C1_M_pkg0 \<rbrace>"
	
definition "shared_variable_events_stm0_C1_M_pkg0 = \<lbrace> 
	  set_EXT_m, 
	  set_EXT_a3, 
	  set_EXT_a1 \<rbrace>"
	
definition "sem__events_stm0_C1_M_pkg0 = \<lbrace> 
	  terminate, 
	  set_EXT_m, 
	  set_EXT_a3, 
	  set_EXT_a1, 
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


locale stm_stm0_C1_M_pkg0
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"Inactive_i0_stm0_C1_M_pkg0 = (SSTOP \<triangle> (Activation_i0_stm0_C1_M_pkg0
  \<box>
  Termination_i0_stm0_C1_M_pkg0))" | 

"Activation_i0_stm0_C1_M_pkg0 = (enter_i0_stm0_C1_M_pkg0 \<rightarrow> Active_i0_stm0_C1_M_pkg0)" | 

"Termination_i0_stm0_C1_M_pkg0 = (terminate \<rightarrow> Skip)" | 

"Active_i0_stm0_C1_M_pkg0 = ((SSTOP \<triangle> (interrupt_i0_stm0_C1_M_pkg0 \<rightarrow> Skip));; Inactive_i0_stm0_C1_M_pkg0)" | 

"Inactive_s0_stm0_C1_M_pkg0 = (SSTOP \<triangle> (Activation_s0_stm0_C1_M_pkg0
  \<box>
  Termination_s0_stm0_C1_M_pkg0))" | 

"Activation_s0_stm0_C1_M_pkg0 = (enter_s0_stm0_C1_M_pkg0 \<rightarrow> Active_s0_stm0_C1_M_pkg0)" | 

"Termination_s0_stm0_C1_M_pkg0 = (terminate \<rightarrow> Skip)" | 

"Active_s0_stm0_C1_M_pkg0 = (((SSTOP \<triangle> (set_a!3 \<rightarrow> Skip));; (CALL__move4();; ((SSTOP \<triangle> (event1_in?(a1) \<rightarrow> (SSTOP \<triangle> (set_a1!a1 \<rightarrow> Skip))));; ((SSTOP \<triangle> (event2_in?(a3) \<rightarrow> (SSTOP \<triangle> (set_a3!a3 \<rightarrow> Skip))));; (SSTOP \<triangle> (get_m?(m) \<rightarrow> (SSTOP \<triangle> (set_m!(m + c1) \<rightarrow> Skip))))))));; (Behaviour_s0_stm0_C1_M_pkg0;; Exiting_s0_stm0_C1_M_pkg0))" | 

"Behaviour_s0_stm0_C1_M_pkg0 = (entered_s0_stm0_C1_M_pkg0 \<rightarrow> During_s0_stm0_C1_M_pkg0)" | 

"During_s0_stm0_C1_M_pkg0 = ((((SSTOP \<triangle> (get_a3?(a3) \<rightarrow> (SSTOP \<triangle> (get_l?(l) \<rightarrow> (SSTOP \<triangle> (set_a!((a3 + l) + 1) \<rightarrow> Skip))))));; CALL__move2(4,5));; SSTOP) \<triangle> (interrupt_s0_stm0_C1_M_pkg0 \<rightarrow> Skip))" | 

"Exiting_s0_stm0_C1_M_pkg0 = ((SSTOP \<triangle> (exit_stm0_C1_M_pkg0 \<rightarrow> Skip));; ((CALL__move1(5);; CALL__move(1,2));; (exited_stm0_C1_M_pkg0 \<rightarrow> Inactive_s0_stm0_C1_M_pkg0)))" | 

"Inactive_f0_stm0_C1_M_pkg0 = (SSTOP \<triangle> (Activation_f0_stm0_C1_M_pkg0
  \<box>
  Termination_f0_stm0_C1_M_pkg0))" | 

"Activation_f0_stm0_C1_M_pkg0 = (enter_f0_stm0_C1_M_pkg0 \<rightarrow> Entering_f0_stm0_C1_M_pkg0)" | 

"Termination_f0_stm0_C1_M_pkg0 = (terminate \<rightarrow> Skip)" | 

"Entering_f0_stm0_C1_M_pkg0 = (entered_f0_stm0_C1_M_pkg0 \<rightarrow> Active_f0_stm0_C1_M_pkg0)" | 

"Active_f0_stm0_C1_M_pkg0 = (SSTOP \<triangle> (Termination_f0_stm0_C1_M_pkg0
  \<box>
  (interrupt_f0_stm0_C1_M_pkg0 \<rightarrow> Interrupted_f0_stm0_C1_M_pkg0)))" | 

"Interrupted_f0_stm0_C1_M_pkg0 = (SSTOP \<triangle> (exit_stm0_C1_M_pkg0 \<rightarrow> (exited_stm0_C1_M_pkg0 \<rightarrow> Inactive)))" | 

"composeNodes = ((Inactive_s0_stm0_C1_M_pkg0
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_f0_stm0_C1_M_pkg0)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_i0_stm0_C1_M_pkg0)" | 

"Trans_stm0_C1_M_pkg0 = (SSTOP \<triangle> (get_a3?(a3) \<rightarrow> (((((((internal__stm0_C1_M_pkg0.(NID_i0_stm0_C1_M_pkg0) \<rightarrow> Skip);; (enter_s0_stm0_C1_M_pkg0 \<rightarrow> Skip))
  \<box>
  ((stop__in.(NID_s0_stm0_C1_M_pkg0) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_C1_M_pkg0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_C1_M_pkg0 \<rightarrow> Skip);; (enter_f0_stm0_C1_M_pkg0 \<rightarrow> Skip))))))
  \<box>
  ((a3 > 4) & (((event2__in.(NID_s0_stm0_C1_M_pkg0)?(a) \<rightarrow> (SSTOP \<triangle> (set_a!a \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_stm0_C1_M_pkg0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_C1_M_pkg0 \<rightarrow> (SSTOP \<triangle> (get_a3?(a3) \<rightarrow> (SSTOP \<triangle> (trigger1_out!(a3 + c2) \<rightarrow> Skip)))));; (enter_s0_stm0_C1_M_pkg0 \<rightarrow> Skip))))))))
  \<box>
  (share \<rightarrow> Skip));; Trans_stm0_C1_M_pkg0)
  \<box>
  (((interrupt_stm0_C1_M_pkg0 \<rightarrow> (SSTOP \<triangle> (exit_stm0_C1_M_pkg0 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0_C1_M_pkg0 \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"ncCoreBehaviour_stm0_C1_M_pkg0 = ((((composeNodes [ interrupt_i0_stm0_C1_M_pkg0 \<mapsto> internal__stm0_C1_M_pkg0\<cdot>NID_i0_stm0_C1_M_pkg0,  
 interrupt_s0_stm0_C1_M_pkg0 \<mapsto> stop__in\<cdot>NID_s0_stm0_C1_M_pkg0,  
 interrupt_s0_stm0_C1_M_pkg0 \<mapsto> event2__in\<cdot>NID_s0_stm0_C1_M_pkg0,  
 interrupt_f0_stm0_C1_M_pkg0 \<mapsto> interrupt_stm0_C1_M_pkg0,  
 interrupt_s0_stm0_C1_M_pkg0 \<mapsto> interrupt_stm0_C1_M_pkg0 ]) [ share \<mapsto> share,  
 set_a3 \<mapsto> setL_a3 ])
  \<lbrakk> | \<lbrace> enter_s0_stm0_C1_M_pkg0,exit_stm0_C1_M_pkg0,exited_stm0_C1_M_pkg0,event2__in\<cdot>NID_s0_stm0_C1_M_pkg0,stop__in\<cdot>NID_s0_stm0_C1_M_pkg0,internal__stm0_C1_M_pkg0\<cdot>NID_i0_stm0_C1_M_pkg0,share,terminate,setL_a3,interrupt_stm0_C1_M_pkg0,enter_f0_stm0_C1_M_pkg0,enter_i0_stm0_C1_M_pkg0 \<rbrace> | \<rbrakk> 
  ((enter_i0_stm0_C1_M_pkg0 \<rightarrow> Trans_stm0_C1_M_pkg0) [ share \<mapsto> share,  
 share \<mapsto> setL_a3 ])) [ setL_a3 \<mapsto> set_a3 ])" | 

"ncBehaviour_stm0_C1_M_pkg0 = ((ncCoreBehaviour_stm0_C1_M_pkg0 \<Zhide> \<lbrace> enter_i0_stm0_C1_M_pkg0,enter_s0_stm0_C1_M_pkg0,enter_f0_stm0_C1_M_pkg0,exit_stm0_C1_M_pkg0,exited_stm0_C1_M_pkg0,internal__stm0_C1_M_pkg0 \<rbrace>) [ stop__in\<cdot>x \<mapsto> stop_in,  
 event2__in\<cdot>x \<mapsto> event2_in ])" | 

"machineBody_stm0_C1_M_pkg0 = ((ncBehaviour_stm0_C1_M_pkg0
  \<lbrakk> | \<lbrace> interrupt_stm0_C1_M_pkg0 \<rbrace> | \<rbrakk> 
  Skip) \<Zhide> \<lbrace> enteredSS_stm0_C1_M_pkg0 \<rbrace>)" | 

"Memory_l(param :: int) = (((get_l!value \<rightarrow> Memory_l(value))
  \<box>
  ((set_l?(x__) \<rightarrow> Memory_l(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"Memory_a(param :: int) = (((get_a!value \<rightarrow> Memory_a(value))
  \<box>
  ((set_a?(x__) \<rightarrow> Memory_a(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"varMemory_stm0_C1_M_pkg0 = (Memory_l(3)
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  Memory_a(0))" | 

"stateful_stm0_C1_M_pkg0 = ((machineBody_stm0_C1_M_pkg0
  \<lbrakk> | \<lbrace> set_a,get_a,get_l,set_l,terminate \<rbrace> | \<rbrakk> 
  varMemory_stm0_C1_M_pkg0) \<Zhide> \<lbrace> set_a,get_a,get_l,set_l,terminate \<rbrace>)" | 

"sharedMemory_m(param :: int) = (((get_m!value \<rightarrow> sharedMemory_m(value))
  \<box>
  ((set_m?(x__) \<rightarrow> sharedMemory_m(x__))
  \<box>
  ((set_EXT_m?(x__) \<rightarrow> sharedMemory_m(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedMemory_a3(param :: int) = (((get_a3!value \<rightarrow> sharedMemory_a3(value))
  \<box>
  ((set_a3?(x__) \<rightarrow> sharedMemory_a3(x__))
  \<box>
  ((set_EXT_a3?(x__) \<rightarrow> sharedMemory_a3(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedMemory_a1(param :: int\<times>int) = (((get_a1!value \<rightarrow> sharedMemory_a1(value))
  \<box>
  ((set_a1?(x__) \<rightarrow> sharedMemory_a1(x__))
  \<box>
  ((set_EXT_a1?(x__) \<rightarrow> sharedMemory_a1(x__))
  \<box>
  (terminate \<rightarrow> Skip)))))" | 

"sharedVarMemory_stm0_C1_M_pkg0 = ((sharedMemory_m(0)
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  sharedMemory_a3(0))
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  sharedMemory_a1(0,0))" | 

"stm_stm0_C1_M_pkg0 = ((((((stateful_stm0_C1_M_pkg0 \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [ share \<mapsto> set_EXT_m,  
 share \<mapsto> set_EXT_a3,  
 share \<mapsto> set_EXT_a1 ])
  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
  Skip)
  \<lbrakk> | \<lbrace> get_a1,get_a3,set_m,set_EXT_a3,set_EXT_m,terminate,set_a3,get_m,set_a1,set_EXT_a1 \<rbrace> | \<rbrakk> 
  sharedVarMemory_stm0_C1_M_pkg0) \<Zhide> \<lbrace> get_a1,get_a3,get_m \<rbrace>)"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess stm_mainaction_stm0_C1_M_pkg0"

end
 
end






theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>

datatype NIDS_stm0_C1_pkg0 = 
	NID_i0_stm0_C1_pkg0 | 
	NID_s0_stm0_C1_pkg0 | 
	NID_f0_stm0_C1_pkg0

\<comment> \<open>Channel Decleration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>internal_channel_stm0_C1_pkg0\<close>

internal__stm0_C1_pkg0 :: NIDS_stm0_C1_pkg0		
	
\<comment> \<open>flowchannel_stm0_C1_pkg0\<close>

interrupt_stm0_C1_pkg0 :: unit 		
exited_stm0_C1_pkg0 :: unit 		
exit_stm0_C1_pkg0 :: unit 		
terminate :: unit 		
	
\<comment> \<open>variable_channel_stm0_C1_pkg0\<close>

get_l_stm0_C1_pkg0 :: int		
set_l_stm0_C1_pkg0 :: int		
setL_l_stm0_C1_pkg0 :: int		
setR_l_stm0_C1_pkg0 :: int		

get_a3_stm0_C1_pkg0 :: int		
set_a3_stm0_C1_pkg0 :: int		
setL_a3_stm0_C1_pkg0 :: int		
setR_a3_stm0_C1_pkg0 :: int		

get_a1_stm0_C1_pkg0 :: int		
set_a1_stm0_C1_pkg0 :: int		
setL_a1_stm0_C1_pkg0 :: int		
setR_a1_stm0_C1_pkg0 :: int		

get_a_stm0_C1_pkg0 :: int		
set_a_stm0_C1_pkg0 :: int		
setL_a_stm0_C1_pkg0 :: int		
setR_a_stm0_C1_pkg0 :: int		

get_m_stm0_C1_pkg0 :: int		
set_m_stm0_C1_pkg0 :: int		
setL_m_stm0_C1_pkg0 :: int		
setR_m_stm0_C1_pkg0 :: int		

get_m1_stm0_C1_pkg0 :: int		
set_m1_stm0_C1_pkg0 :: int		
setL_m1_stm0_C1_pkg0 :: int		
setR_m1_stm0_C1_pkg0 :: int		

get_a2_stm0_C1_pkg0 :: int		
set_a2_stm0_C1_pkg0 :: int		
setL_a2_stm0_C1_pkg0 :: int		
setR_a2_stm0_C1_pkg0 :: int		
	
\<comment> \<open>event_channel_stm0_C1_pkg0\<close>

stop_stm0_C1_pkg0_in :: unit 		
stop_stm0_C1_pkg0_out :: unit 		

event1_stm0_C1_pkg0_in :: int		
event1_stm0_C1_pkg0_out :: int		

event2_stm0_C1_pkg0_in :: int		
event2_stm0_C1_pkg0_out :: int		

trigger1_stm0_C1_pkg0_in :: int		
trigger1_stm0_C1_pkg0_out :: int		

stop_stm0_C1_pkg0__in :: NIDS_stm0_C1_pkg0		

event1_stm0_C1_pkg0__in :: "NIDS_stm0_C1_pkg0\<times>int"		

event2_stm0_C1_pkg0__in :: "NIDS_stm0_C1_pkg0\<times>int"		

trigger1_stm0_C1_pkg0__in :: "NIDS_stm0_C1_pkg0\<times>int"		
	
\<comment> \<open>junction_channel_i0_stm0_C1_pkg0\<close>

enter_i0_stm0_C1_pkg0 :: unit 		
interrupt_i0_stm0_C1_pkg0 :: unit 		
	
\<comment> \<open>state_channel_s0_stm0_C1_pkg0\<close>

enter_s0_stm0_C1_pkg0 :: unit 		
entered_s0_stm0_C1_pkg0 :: unit 		
interrupt_s0_stm0_C1_pkg0 :: unit 		
enteredL_s0_stm0_C1_pkg0 :: unit 		
enteredR_s0_stm0_C1_pkg0 :: unit 		
	
\<comment> \<open>state_channel_f0_stm0_C1_pkg0\<close>

enter_f0_stm0_C1_pkg0 :: unit 		
entered_f0_stm0_C1_pkg0 :: unit 		
interrupt_f0_stm0_C1_pkg0 :: unit 		
enteredL_f0_stm0_C1_pkg0 :: unit 		
enteredR_f0_stm0_C1_pkg0 :: unit 		
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_stm0_C1_pkg0 = \<lbrace> 
	  enter_i0_stm0_C1_pkg0, 
	  enter_s0_stm0_C1_pkg0, 
	  enter_f0_stm0_C1_pkg0 \<rbrace>"
	
definition "enteredSS_stm0_C1_pkg0 = \<lbrace> 
	  entered_s0_stm0_C1_pkg0, 
	  entered_f0_stm0_C1_pkg0 \<rbrace>"
	
definition "internal_events_stm0_C1_pkg0 = \<lbrace> 
	  enter_i0_stm0_C1_pkg0, 
	  enter_s0_stm0_C1_pkg0, 
	  enter_f0_stm0_C1_pkg0, 
	  entered_s0_stm0_C1_pkg0, 
	  entered_f0_stm0_C1_pkg0, 
	  interrupt_stm0_C1_pkg0, 
	  exited_stm0_C1_pkg0 \<rbrace>"
	
definition "sem__events_stm0_C1_pkg0 = \<lbrace> 
	  terminate, 
	  stop_stm0_C1_pkg0_in, 
	  stop_stm0_C1_pkg0_out, 
	  event1_stm0_C1_pkg0_in, 
	  event1_stm0_C1_pkg0_out, 
	  event2_stm0_C1_pkg0_in, 
	  event2_stm0_C1_pkg0_out, 
	  trigger1_stm0_C1_pkg0_in, 
	  trigger1_stm0_C1_pkg0_out \<rbrace>"
	
definition "ncCoreBeh_hideset_stm0_C1_pkg0 = \<lbrace> 
	  enter_i0_stm0_C1_pkg0, 
	  enter_s0_stm0_C1_pkg0, 
	  enter_f0_stm0_C1_pkg0, 
	  exit_stm0_C1_pkg0, 
	  exited_stm0_C1_pkg0, 
	  internal__stm0_C1_pkg0 \<rbrace>"
	
definition "parallel_chanset_ncCoreBeh_stm0_C1_pkg0 = \<lbrace> 
	  enter_s0_stm0_C1_pkg0, 
	  exit_stm0_C1_pkg0, 
	  exited_stm0_C1_pkg0, 
	  stop_stm0_C1_pkg0__in.s0_stm0_C1_pkg0, 
	  share, 
	  enter_f0_stm0_C1_pkg0, 
	  terminate, 
	  interrupt_stm0_C1_pkg0, 
	  event2_stm0_C1_pkg0__in.s0_stm0_C1_pkg0, 
	  enter_i0_stm0_C1_pkg0, 
	  internal__stm0_C1_pkg0.NID_i0_stm0_C1_pkg0 \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
	"relu x = max 0 x"

locale state_proc_i0_stm0_C1_pkg0
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 
"Activation = (enter_i0_stm0_C1_pkg0 \<rightarrow> Active)" | 
"Termination = (terminate \<rightarrow> Skip)" | 
"Active = ((SSTOP \<triangle> (interrupt_i0_stm0_C1_pkg0 \<rightarrow> Skip));; Inactive)"

\<comment> \<open>Main action of the process\<close>
definition "MainAction = cProcess Inactive"
end

locale state_proc_s0_stm0_C1_pkg0
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 
"Activation = (enter_s0_stm0_C1_pkg0 \<rightarrow> Active)" | 
"Termination = (terminate \<rightarrow> Skip)" | 
"Active = ((SSTOP \<triangle> (event1_stm0_C1_pkg0_in?(a1_stm0_C1_pkg0) \<rightarrow> (SSTOP \<triangle> (set_a1_stm0_C1_pkg0!a1_stm0_C1_pkg0 \<rightarrow> Skip))));; (Behaviour;; Exiting))" | 
"Behaviour = (entered_s0_stm0_C1_pkg0 \<rightarrow> During)" | 
"During = (((SSTOP \<triangle> (get_a1_stm0_C1_pkg0?(a1_stm0_C1_pkg0) \<rightarrow> (SSTOP \<triangle> (get_l_stm0_C1_pkg0?(l_stm0_C1_pkg0) \<rightarrow> (SSTOP \<triangle> (set_a_stm0_C1_pkg0!((a1_stm0_C1_pkg0 + l_stm0_C1_pkg0) + 1) \<rightarrow> Skip))))));; SSTOP) \<triangle> (interrupt_s0_stm0_C1_pkg0 \<rightarrow> Skip))" | 
"Exiting = ((SSTOP \<triangle> (exit_stm0_C1_pkg0 \<rightarrow> Skip));; (Skip;; (exited_stm0_C1_pkg0 \<rightarrow> Inactive)))"

\<comment> \<open>Main action of the process\<close>
definition "MainAction = cProcess Inactive"
end

locale state_proc_f0_stm0_C1_pkg0
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 
"Activation = (enter_f0_stm0_C1_pkg0 \<rightarrow> Entering)" | 
"Termination = (terminate \<rightarrow> Skip)" | 
"Entering = (entered_f0_stm0_C1_pkg0 \<rightarrow> Active)" | 
"Active = (SSTOP \<triangle> (Termination
  \<box>
  (interrupt_f0_stm0_C1_pkg0 \<rightarrow> Interrupted)))" | 
"Interrupted = (SSTOP \<triangle> (exit_stm0_C1_pkg0 \<rightarrow> (exited_stm0_C1_pkg0 \<rightarrow> Inactive)))"

\<comment> \<open>Main action of the process\<close>
definition "MainAction = cProcess Inactive"
end

locale trans_proc_stm0_C1_pkg0
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"prefixedTransAction_stm0 = (enter_i0_stm0_C1_pkg0 \<rightarrow> (((((((internal__stm0_C1_pkg0 \<rightarrow> Skip);; (enter_s0_stm0_C1_pkg0 \<rightarrow> Skip))
  \<box>
  ((stop_stm0_C1_pkg0__in \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm0_C1_pkg0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_C1_pkg0 \<rightarrow> Skip);; (enter_f0_stm0_C1_pkg0 \<rightarrow> Skip))))))
  \<box>
  ((event2_stm0_C1_pkg0__in!NID_s0_stm0_C1_pkg0 \<rightarrow> (SSTOP \<triangle> (set_a_stm0_C1_pkg0!a_stm0_C1_pkg0 \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_stm0_C1_pkg0 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_C1_pkg0 \<rightarrow> (SSTOP \<triangle> (get_a1_stm0_C1_pkg0?(a1_stm0_C1_pkg0) \<rightarrow> (SSTOP \<triangle> (trigger1_stm0_C1_pkg0_out!a1_stm0_C1_pkg0 \<rightarrow> Skip)))));; (enter_s0_stm0_C1_pkg0 \<rightarrow> Skip))))))
  \<box>
  (share \<rightarrow> Skip));; trans)
  \<box>
  (((interrupt_stm0_C1_pkg0 \<rightarrow> (SSTOP \<triangle> (exit_stm0_C1_pkg0 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0_C1_pkg0 \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip))))"

\<comment> \<open>Main action of the process\<close>
definition "MainAction = cProcess prefixedTransAction_stm0"
end

locale ncBehaviourProc_stm0_C1_pkg0
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
" ncBehaviourProc_stm0_C1_pkg0 = 
	((((((((state_proc_i0_stm0_C1_pkg0 \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> state_proc_f0_stm0_C1_pkg0) \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> state_proc_s0_stm0_C1_pkg0)
	  [ interrupt_i0_stm0_C1_pkg0\<mapsto>internal__stm0_C1_pkg0.NID_i0_stm0_C1_pkg0,  
	 interrupt_s0_stm0_C1_pkg0\<mapsto>stop_stm0_C1_pkg0__in.s0_stm0_C1_pkg0,  
	 interrupt_s0_stm0_C1_pkg0\<mapsto>event2_stm0_C1_pkg0__in.s0_stm0_C1_pkg0,  
	 interrupt_s0_stm0_C1_pkg0\<mapsto>interrupt_stm0_C1_pkg0,  
	 interrupt_f0_stm0_C1_pkg0\<mapsto>interrupt_stm0_C1_pkg0 ])
	  [ share\<mapsto>share ]) \<lbrakk> | parallel_chanset_ncCoreBeh_stm0_C1_pkg0 | \<rbrakk> (trans_proc_stm0_C1_pkg0
	  [ share\<mapsto>share ]))
	  [  ]) \<Zhide> ncCoreBeh_hideset_stm0_C1_pkg0)
	  [ event2_stm0_C1_pkg0__in\<cdot>x\<mapsto>event2_stm0_C1_pkg0_in,  
	 stop_stm0_C1_pkg0__in\<cdot>x\<mapsto>stop_stm0_C1_pkg0_in ]) "

\<comment> \<open>Main action of the process\<close>
definition "MainAction = cProcess ncBehaviourProc_stm0_C1_pkg0.MainAction"
end
 
end





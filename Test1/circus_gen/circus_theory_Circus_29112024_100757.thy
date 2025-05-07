theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm0_C1_pkg1 = 
	NID_i0_stm0_C1_pkg1 | 
	NID_s0_stm0_C1_pkg1 | 
	NID_f0_stm0_C1_pkg1



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>internal_channel_stm0_C1_pkg1\<close>

internal__stm0_C1_pkg1 :: "NIDS_stm0_C1_pkg1"
	
\<comment> \<open>flowchannel_stm0_C1_pkg1\<close>

interrupt_stm0_C1_pkg1 :: unit 
exited_stm0_C1_pkg1 :: unit 
exit_stm0_C1_pkg1 :: unit 
terminate :: unit 
	
\<comment> \<open>variable_channel_stm0_C1_pkg1\<close>

get_l_stm0_C1_pkg1 :: "int"
set_l_stm0_C1_pkg1 :: "int"
setL_l_stm0_C1_pkg1 :: "int"
setR_l_stm0_C1_pkg1 :: "int"

get_a_stm0_C1_pkg1 :: "int"
set_a_stm0_C1_pkg1 :: "int"
setL_a_stm0_C1_pkg1 :: "int"
setR_a_stm0_C1_pkg1 :: "int"

get_m_stm0_C1_pkg1 :: "int"
set_m_stm0_C1_pkg1 :: "int"
setL_m_stm0_C1_pkg1 :: "int"
setR_m_stm0_C1_pkg1 :: "int"

get_a1_stm0_C1_pkg1 :: "int"
set_a1_stm0_C1_pkg1 :: "int"
setL_a1_stm0_C1_pkg1 :: "int"
setR_a1_stm0_C1_pkg1 :: "int"
	
\<comment> \<open>event_channel_stm0_C1_pkg1\<close>

stop_stm0_C1_pkg1_in :: unit 
stop_stm0_C1_pkg1_out :: unit 

event1_stm0_C1_pkg1_in :: "int"
event1_stm0_C1_pkg1_out :: "int"

event2_stm0_C1_pkg1_in :: "int"
event2_stm0_C1_pkg1_out :: "int"

trigger1_stm0_C1_pkg1_in :: "int"
trigger1_stm0_C1_pkg1_out :: "int"

stop_stm0_C1_pkg1__in :: "NIDS_stm0_C1_pkg1"

event1_stm0_C1_pkg1__in :: "NIDS_stm0_C1_pkg1\<times>int"

event2_stm0_C1_pkg1__in :: "NIDS_stm0_C1_pkg1\<times>int"

trigger1_stm0_C1_pkg1__in :: "NIDS_stm0_C1_pkg1\<times>int"
	
\<comment> \<open>junction_channel_i0_stm0_C1_pkg1\<close>

enter_i0_stm0_C1_pkg1 :: unit 
interrupt_i0_stm0_C1_pkg1 :: unit 
	
\<comment> \<open>state_channel_s0_stm0_C1_pkg1\<close>

enter_s0_stm0_C1_pkg1 :: unit 
entered_s0_stm0_C1_pkg1 :: unit 
interrupt_s0_stm0_C1_pkg1 :: unit 
enteredL_s0_stm0_C1_pkg1 :: unit 
enteredR_s0_stm0_C1_pkg1 :: unit 
	
\<comment> \<open>state_channel_f0_stm0_C1_pkg1\<close>

enter_f0_stm0_C1_pkg1 :: unit 
entered_f0_stm0_C1_pkg1 :: unit 
interrupt_f0_stm0_C1_pkg1 :: unit 
enteredL_f0_stm0_C1_pkg1 :: unit 
enteredR_f0_stm0_C1_pkg1 :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_stm0_C1_pkg1 = \<lbrace> 
	  enter_i0_stm0_C1_pkg1, 
	  enter_s0_stm0_C1_pkg1, 
	  enter_f0_stm0_C1_pkg1 \<rbrace>"
	
definition "enteredSS_stm0_C1_pkg1 = \<lbrace> 
	  entered_f0_stm0_C1_pkg1, 
	  entered_s0_stm0_C1_pkg1 \<rbrace>"
	
definition "internal_events_stm0_C1_pkg1 = \<lbrace> 
	  enter_i0_stm0_C1_pkg1, 
	  enter_s0_stm0_C1_pkg1, 
	  enter_f0_stm0_C1_pkg1, 
	  entered_f0_stm0_C1_pkg1, 
	  entered_s0_stm0_C1_pkg1, 
	  interrupt_stm0_C1_pkg1, 
	  exited_stm0_C1_pkg1 \<rbrace>"
	
definition "sem__events_stm0_C1_pkg1 = \<lbrace> 
	  terminate, 
	  stop_stm0_C1_pkg1_in, 
	  stop_stm0_C1_pkg1_out, 
	  event1_stm0_C1_pkg1_in, 
	  event1_stm0_C1_pkg1_out, 
	  event2_stm0_C1_pkg1_in, 
	  event2_stm0_C1_pkg1_out, 
	  trigger1_stm0_C1_pkg1_in, 
	  trigger1_stm0_C1_pkg1_out \<rbrace>"
	
definition "ncCoreBeh_hideset_stm0_C1_pkg1 = \<lbrace> 
	  enter_i0_stm0_C1_pkg1, 
	  enter_s0_stm0_C1_pkg1, 
	  enter_f0_stm0_C1_pkg1, 
	  exit_stm0_C1_pkg1, 
	  exited_stm0_C1_pkg1, 
	  internal__stm0_C1_pkg1 \<rbrace>"
	
definition "parallel_chanset_ncCoreBeh_stm0_C1_pkg1 = \<lbrace> 
	  enter_s0_stm0_C1_pkg1, 
	  event1_stm0_C1_pkg1__in.NID_s0_stm0_C1_pkg1, 
	  SetL_a_stm0_C1_pkg1, 
	  exit_stm0_C1_pkg1, 
	  internal__stm0_C1_pkg1.NID_i0_stm0_C1_pkg1, 
	  event2_stm0_C1_pkg1__in.NID_s0_stm0_C1_pkg1, 
	  exited_stm0_C1_pkg1, 
	  enter_i0_stm0_C1_pkg1, 
	  enter_f0_stm0_C1_pkg1, 
	  share, 
	  terminate, 
	  interrupt_stm0_C1_pkg1 \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
	"relu x = max 0 x"


locale state_proc_i0_stm0_C1_pkg1
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 

"Activation = (enter_i0_stm0_C1_pkg1 \<rightarrow> Active)" | 

"Termination = (terminate \<rightarrow> Skip)" | 

"Active = ((SSTOP \<triangle> (interrupt_i0_stm0_C1_pkg1 \<rightarrow> Skip));; Inactive)"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess Inactive"

end

locale state_proc_s0_stm0_C1_pkg1
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 

"Activation = (enter_s0_stm0_C1_pkg1 \<rightarrow> Active)" | 

"Termination = (terminate \<rightarrow> Skip)" | 

"Active = ((SSTOP \<triangle> (event1_stm0_C1_pkg1_in\<^bold>?(a1_stm0_C1_pkg1) \<rightarrow> (SSTOP \<triangle> (set_a1_stm0_C1_pkg1\<^bold>!a1_stm0_C1_pkg1 \<rightarrow> Skip))));; (Behaviour;; Exiting))" | 

"Behaviour = (entered_s0_stm0_C1_pkg1 \<rightarrow> During)" | 

"During = (((SSTOP \<triangle> (get_a1_stm0_C1_pkg1\<^bold>?(a1_stm0_C1_pkg1) \<rightarrow> (SSTOP \<triangle> (get_l_stm0_C1_pkg1\<^bold>?(l_stm0_C1_pkg1) \<rightarrow> (SSTOP \<triangle> (set_a_stm0_C1_pkg1\<^bold>!((a1_stm0_C1_pkg1 + l_stm0_C1_pkg1) + 1) \<rightarrow> Skip))))));; SSTOP) \<triangle> (interrupt_s0_stm0_C1_pkg1 \<rightarrow> Skip))" | 

"Exiting = ((SSTOP \<triangle> (exit_stm0_C1_pkg1 \<rightarrow> Skip));; (Skip;; (exited_stm0_C1_pkg1 \<rightarrow> Inactive)))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess Inactive"

end

locale state_proc_f0_stm0_C1_pkg1
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 

"Activation = (enter_f0_stm0_C1_pkg1 \<rightarrow> Entering)" | 

"Termination = (terminate \<rightarrow> Skip)" | 

"Entering = (entered_f0_stm0_C1_pkg1 \<rightarrow> Active)" | 

"Active = (SSTOP \<triangle> (Termination
  \<box>
  (interrupt_f0_stm0_C1_pkg1 \<rightarrow> Interrupted)))" | 

"Interrupted = (SSTOP \<triangle> (exit_stm0_C1_pkg1 \<rightarrow> (exited_stm0_C1_pkg1 \<rightarrow> Inactive)))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess Inactive"

end

locale trans_proc_stm0_C1_pkg1
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"prefixedTransAction_stm0 = (enter_i0_stm0_C1_pkg1 \<rightarrow> (SSTOP \<triangle> (get_a_stm0_C1_pkg1\<^bold>?(a_stm0_C1_pkg1) \<rightarrow> (((((((internal__stm0_C1_pkg1\<^bold>.(NID_i0_stm0_C1_pkg1) \<rightarrow> Skip);; (enter_s0_stm0_C1_pkg1 \<rightarrow> Skip))
  \<box>
  ((a_stm0_C1_pkg1 > 4) \<^bold>& (((event1_stm0_C1_pkg1__in\<^bold>.(NID_s0_stm0_C1_pkg1)\<^bold>?(a1_stm0_C1_pkg1) \<rightarrow> (SSTOP \<triangle> (set_a1_stm0_C1_pkg1\<^bold>!a1_stm0_C1_pkg1 \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_stm0_C1_pkg1 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_C1_pkg1 \<rightarrow> Skip);; (enter_f0_stm0_C1_pkg1 \<rightarrow> Skip))))))))
  \<box>
  ((event2_stm0_C1_pkg1__in\<^bold>.(NID_s0_stm0_C1_pkg1)\<^bold>?(a_stm0_C1_pkg1) \<rightarrow> (SSTOP \<triangle> (set_a_stm0_C1_pkg1\<^bold>!a_stm0_C1_pkg1 \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_stm0_C1_pkg1 \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm0_C1_pkg1 \<rightarrow> (SSTOP \<triangle> (get_a1_stm0_C1_pkg1\<^bold>?(a1_stm0_C1_pkg1) \<rightarrow> (SSTOP \<triangle> (trigger1_stm0_C1_pkg1_out\<^bold>!a1_stm0_C1_pkg1 \<rightarrow> Skip)))));; (enter_s0_stm0_C1_pkg1 \<rightarrow> Skip))))))
  \<box>
  (share \<rightarrow> Skip));; trans)
  \<box>
  (((interrupt_stm0_C1_pkg1 \<rightarrow> (SSTOP \<triangle> (exit_stm0_C1_pkg1 \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm0_C1_pkg1 \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip))))))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess prefixedTransAction_stm0"

end

locale ncBehaviourProc_stm0_C1_pkg1
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

" ncBehaviourProc_stm0_C1_pkg1 = 
	((((((((state_proc_s0_stm0_C1_pkg1 \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> state_proc_f0_stm0_C1_pkg1) \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> state_proc_i0_stm0_C1_pkg1)
	  [ interrupt_i0_stm0_C1_pkg1 \<mapsto> internal__stm0_C1_pkg1.NID_i0_stm0_C1_pkg1,  
	 interrupt_s0_stm0_C1_pkg1 \<mapsto> event1_stm0_C1_pkg1__in.NID_s0_stm0_C1_pkg1,  
	 interrupt_s0_stm0_C1_pkg1 \<mapsto> event2_stm0_C1_pkg1__in.NID_s0_stm0_C1_pkg1,  
	 interrupt_f0_stm0_C1_pkg1 \<mapsto> interrupt_stm0_C1_pkg1,  
	 interrupt_s0_stm0_C1_pkg1 \<mapsto> interrupt_stm0_C1_pkg1 ])
	  [ share \<mapsto> share,  
	 set_a_stm0_C1_pkg1 \<mapsto> setL_a_stm0_C1_pkg1 ]) \<lbrakk> | parallel_chanset_ncCoreBeh_stm0_C1_pkg1 | \<rbrakk> (trans_proc_stm0_C1_pkg1
	  [ share \<mapsto> share,  
	 share \<mapsto> setL_a_stm0_C1_pkg1 ]))
	  [ setL_a_stm0_C1_pkg1 \<mapsto> set_a_stm0_C1_pkg1 ]) \<Zhide> ncCoreBeh_hideset_stm0_C1_pkg1)
	  [ event1_stm0_C1_pkg1__in\<cdot>x \<mapsto> event1_stm0_C1_pkg1_in,  
	 event2_stm0_C1_pkg1__in\<cdot>x \<mapsto> event2_stm0_C1_pkg1_in ]) "

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess ncBehaviourProc_stm0_C1_pkg1.ProcDef"

end
 
end






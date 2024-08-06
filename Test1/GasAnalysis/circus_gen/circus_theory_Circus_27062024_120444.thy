theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>

type_synonym Chem = nat
type_synonym Intensity = nat

	
	
datatype Status = 
	noGas | 
	gasD	
	
datatype Angle = 
	Left | 
	Right | 
	Back | 
	Front	
	
datatype NIDS_GasAnalysis_Chemical = 
	NID_i1_GasAnalysis_Chemical | 
	NID_GasDetected_GasAnalysis_Chemical | 
	NID_j1_GasAnalysis_Chemical | 
	NID_Reading_GasAnalysis_Chemical | 
	NID_Analysis_GasAnalysis_Chemical | 
	NID_NoGas_GasAnalysis_Chemical

record GasSensor =
	c :: "Chem"
	i :: "Intensity"


\<comment> \<open>constant declaration\<close>
consts thr :: Intensity


\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>internal_channel_GasAnalysis_Chemical\<close>

internal__GasAnalysis_Chemical :: "NIDS_GasAnalysis_Chemical"
	
\<comment> \<open>flowchannel_GasAnalysis_Chemical\<close>

interrupt_GasAnalysis_Chemical :: unit 
exited_GasAnalysis_Chemical :: unit 
exit_GasAnalysis_Chemical :: unit 
terminate :: unit 
	
\<comment> \<open>variable_channel_GasAnalysis_Chemical\<close>

get_sts :: "Status"
set_sts :: "Status"
setL_sts :: "Status"
setR_sts :: "Status"

get_gs :: "(GasSensor list)"
set_gs :: "(GasSensor list)"
setL_gs :: "(GasSensor list)"
setR_gs :: "(GasSensor list)"

get_ins :: "Intensity"
set_ins :: "Intensity"
setL_ins :: "Intensity"
setR_ins :: "Intensity"

get_anl :: "Angle"
set_anl :: "Angle"
setL_anl :: "Angle"
setR_anl :: "Angle"
	
\<comment> \<open>event_channel_GasAnalysis_Chemical\<close>

gas_in :: "(GasSensor list)"
gas_out :: "(GasSensor list)"

resume_in :: unit 
resume_out :: unit 

turn_in :: "Angle"
turn_out :: "Angle"

stop_in :: unit 
stop_out :: unit 

gas__in :: "NIDS_GasAnalysis_Chemical\<times>(GasSensor list)"

resume__in :: "NIDS_GasAnalysis_Chemical"

turn__in :: "NIDS_GasAnalysis_Chemical\<times>Angle"

stop__in :: "NIDS_GasAnalysis_Chemical"
	
\<comment> \<open>junction_channel_i1_GasAnalysis_Chemical\<close>

enter_i1_GasAnalysis_Chemical :: unit 
interrupt_i1_GasAnalysis_Chemical :: unit 
	
\<comment> \<open>state_channel_GasDetected_GasAnalysis_Chemical\<close>

enter_GasDetected_GasAnalysis_Chemical :: unit 
entered_GasDetected_GasAnalysis_Chemical :: unit 
interrupt_GasDetected_GasAnalysis_Chemical :: unit 
enteredL_GasDetected_GasAnalysis_Chemical :: unit 
enteredR_GasDetected_GasAnalysis_Chemical :: unit 
	
\<comment> \<open>state_channel_j1_GasAnalysis_Chemical\<close>

enter_j1_GasAnalysis_Chemical :: unit 
entered_j1_GasAnalysis_Chemical :: unit 
interrupt_j1_GasAnalysis_Chemical :: unit 
enteredL_j1_GasAnalysis_Chemical :: unit 
enteredR_j1_GasAnalysis_Chemical :: unit 
	
\<comment> \<open>state_channel_Reading_GasAnalysis_Chemical\<close>

enter_Reading_GasAnalysis_Chemical :: unit 
entered_Reading_GasAnalysis_Chemical :: unit 
interrupt_Reading_GasAnalysis_Chemical :: unit 
enteredL_Reading_GasAnalysis_Chemical :: unit 
enteredR_Reading_GasAnalysis_Chemical :: unit 
	
\<comment> \<open>state_channel_Analysis_GasAnalysis_Chemical\<close>

enter_Analysis_GasAnalysis_Chemical :: unit 
entered_Analysis_GasAnalysis_Chemical :: unit 
interrupt_Analysis_GasAnalysis_Chemical :: unit 
enteredL_Analysis_GasAnalysis_Chemical :: unit 
enteredR_Analysis_GasAnalysis_Chemical :: unit 
	
\<comment> \<open>state_channel_NoGas_GasAnalysis_Chemical\<close>

enter_NoGas_GasAnalysis_Chemical :: unit 
entered_NoGas_GasAnalysis_Chemical :: unit 
interrupt_NoGas_GasAnalysis_Chemical :: unit 
enteredL_NoGas_GasAnalysis_Chemical :: unit 
enteredR_NoGas_GasAnalysis_Chemical :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_GasAnalysis_Chemical = \<lbrace> 
	  enter_i1_GasAnalysis_Chemical, 
	  enter_GasDetected_GasAnalysis_Chemical, 
	  enter_j1_GasAnalysis_Chemical, 
	  enter_Reading_GasAnalysis_Chemical, 
	  enter_Analysis_GasAnalysis_Chemical, 
	  enter_NoGas_GasAnalysis_Chemical \<rbrace>"
	
definition "enteredSS_GasAnalysis_Chemical = \<lbrace> 
	  entered_j1_GasAnalysis_Chemical, 
	  entered_NoGas_GasAnalysis_Chemical, 
	  entered_Reading_GasAnalysis_Chemical, 
	  entered_GasDetected_GasAnalysis_Chemical, 
	  entered_Analysis_GasAnalysis_Chemical \<rbrace>"
	
definition "internal_events_GasAnalysis_Chemical = \<lbrace> 
	  enter_i1_GasAnalysis_Chemical, 
	  enter_GasDetected_GasAnalysis_Chemical, 
	  enter_j1_GasAnalysis_Chemical, 
	  enter_Reading_GasAnalysis_Chemical, 
	  enter_Analysis_GasAnalysis_Chemical, 
	  enter_NoGas_GasAnalysis_Chemical, 
	  entered_j1_GasAnalysis_Chemical, 
	  entered_NoGas_GasAnalysis_Chemical, 
	  entered_Reading_GasAnalysis_Chemical, 
	  entered_GasDetected_GasAnalysis_Chemical, 
	  entered_Analysis_GasAnalysis_Chemical, 
	  interrupt_GasAnalysis_Chemical, 
	  exited_GasAnalysis_Chemical \<rbrace>"
	
definition "sem__events_GasAnalysis_Chemical = \<lbrace> 
	  terminate, 
	  gas_in, 
	  gas_out, 
	  resume_in, 
	  resume_out, 
	  turn_in, 
	  turn_out, 
	  stop_in, 
	  stop_out \<rbrace>"
	
definition "ncCoreBeh_hideset_GasAnalysis_Chemical = \<lbrace> 
	  enter_i1_GasAnalysis_Chemical, 
	  enter_GasDetected_GasAnalysis_Chemical, 
	  enter_j1_GasAnalysis_Chemical, 
	  enter_Reading_GasAnalysis_Chemical, 
	  enter_Analysis_GasAnalysis_Chemical, 
	  enter_NoGas_GasAnalysis_Chemical, 
	  exit_GasAnalysis_Chemical, 
	  exited_GasAnalysis_Chemical, 
	  internal__GasAnalysis_Chemical \<rbrace>"
	
definition "parallel_chanset_ncCoreBeh_GasAnalysis_Chemical = \<lbrace> 
	  internal__GasAnalysis_Chemical\<cdot>NID_i1_GasAnalysis_Chemical, 
	  internal__GasAnalysis_Chemical\<cdot>NID_Analysis_GasAnalysis_Chemical, 
	  exited_GasAnalysis_Chemical, 
	  enter_GasDetected_GasAnalysis_Chemical, 
	  gas__in\<cdot>NID_Reading_GasAnalysis_Chemical, 
	  enter_Analysis_GasAnalysis_Chemical, 
	  interrupt_GasAnalysis_Chemical, 
	  enter_i1_GasAnalysis_Chemical, 
	  internal__GasAnalysis_Chemical\<cdot>NID_NoGas_GasAnalysis_Chemical, 
	  setL_ins, 
	  enter_NoGas_GasAnalysis_Chemical, 
	  setL_sts, 
	  enter_j1_GasAnalysis_Chemical, 
	  enter_Reading_GasAnalysis_Chemical, 
	  internal__GasAnalysis_Chemical\<cdot>NID_GasDetected_GasAnalysis_Chemical, 
	  exit_GasAnalysis_Chemical, 
	  share, 
	  terminate \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
	"relu x = max 0 x"

locale node_proc_i1_GasAnalysis_Chemical
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 
"Activation = (enter_i1_GasAnalysis_Chemical \<rightarrow> Active)" | 
"Termination = (terminate \<rightarrow> Skip)" | 
"Active = ((SSTOP \<triangle> (interrupt_i1_GasAnalysis_Chemical \<rightarrow> Skip));; Inactive)"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess Inactive"

end

locale node_proc_GasDetected_GasAnalysis_Chemical
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 
"Activation = (enter_GasDetected_GasAnalysis_Chemical \<rightarrow> Active)" | 
"Termination = (terminate \<rightarrow> Skip)" | 
"Active = ((SSTOP \<triangle> (get_gs?(gs) \<rightarrow> (SSTOP \<triangle> (set_ins!intensity(gs) \<rightarrow> Skip))));; (Behaviour;; Exiting))" | 
"Behaviour = (entered_GasDetected_GasAnalysis_Chemical \<rightarrow> During)" | 
"During = ((Skip;; SSTOP) \<triangle> (interrupt_GasDetected_GasAnalysis_Chemical \<rightarrow> Skip))" | 
"Exiting = ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (Skip;; (exited_GasAnalysis_Chemical \<rightarrow> Inactive)))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess Inactive"

end

locale node_proc_j1_GasAnalysis_Chemical
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 
"Activation = (enter_j1_GasAnalysis_Chemical \<rightarrow> Entering)" | 
"Termination = (terminate \<rightarrow> Skip)" | 
"Entering = (entered_j1_GasAnalysis_Chemical \<rightarrow> Active)" | 
"Active = (SSTOP \<triangle> (Termination
  \<box>
  (interrupt_j1_GasAnalysis_Chemical \<rightarrow> Interrupted)))" | 
"Interrupted = (SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> (exited_GasAnalysis_Chemical \<rightarrow> Inactive)))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess Inactive"

end

locale node_proc_Reading_GasAnalysis_Chemical
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 
"Activation = (enter_Reading_GasAnalysis_Chemical \<rightarrow> Active)" | 
"Termination = (terminate \<rightarrow> Skip)" | 
"Active = (Skip;; (Behaviour;; Exiting))" | 
"Behaviour = (entered_Reading_GasAnalysis_Chemical \<rightarrow> During)" | 
"During = ((Skip;; SSTOP) \<triangle> (interrupt_Reading_GasAnalysis_Chemical \<rightarrow> Skip))" | 
"Exiting = ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (Skip;; (exited_GasAnalysis_Chemical \<rightarrow> Inactive)))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess Inactive"

end

locale node_proc_Analysis_GasAnalysis_Chemical
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 
"Activation = (enter_Analysis_GasAnalysis_Chemical \<rightarrow> Active)" | 
"Termination = (terminate \<rightarrow> Skip)" | 
"Active = ((SSTOP \<triangle> (get_gs?(gs) \<rightarrow> (SSTOP \<triangle> (set_sts!analysis(gs) \<rightarrow> Skip))));; (Behaviour;; Exiting))" | 
"Behaviour = (entered_Analysis_GasAnalysis_Chemical \<rightarrow> During)" | 
"During = ((Skip;; SSTOP) \<triangle> (interrupt_Analysis_GasAnalysis_Chemical \<rightarrow> Skip))" | 
"Exiting = ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (Skip;; (exited_GasAnalysis_Chemical \<rightarrow> Inactive)))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess Inactive"

end

locale node_proc_NoGas_GasAnalysis_Chemical
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Inactive = (SSTOP \<triangle> (Activation
  \<box>
  Termination))" | 
"Activation = (enter_NoGas_GasAnalysis_Chemical \<rightarrow> Active)" | 
"Termination = (terminate \<rightarrow> Skip)" | 
"Active = (Skip;; (Behaviour;; Exiting))" | 
"Behaviour = (entered_NoGas_GasAnalysis_Chemical \<rightarrow> During)" | 
"During = ((Skip;; SSTOP) \<triangle> (interrupt_NoGas_GasAnalysis_Chemical \<rightarrow> Skip))" | 
"Exiting = ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (Skip;; (exited_GasAnalysis_Chemical \<rightarrow> Inactive)))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess Inactive"

end

locale trans_proc_GasAnalysis_Chemical
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"prefixedTransAction_GasAnalysis_Chemical = (enter_i1_GasAnalysis_Chemical \<rightarrow> (SSTOP \<triangle> (get_sts?(sts) \<rightarrow> (get_ins?(ins) \<rightarrow> (((((((((((internal__GasAnalysis_Chemical.(NID_i1_GasAnalysis_Chemical) \<rightarrow> ((SSTOP \<triangle> (set_gs![] \<rightarrow> Skip));; (SSTOP \<triangle> (set_anl!Front \<rightarrow> Skip))));; (enter_Reading_GasAnalysis_Chemical \<rightarrow> Skip))
  \<box>
  ((gas__in.(NID_Reading_GasAnalysis_Chemical)?(gs) \<rightarrow> (SSTOP \<triangle> (set_gs!gs \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> Skip);; (enter_Analysis_GasAnalysis_Chemical \<rightarrow> Skip))))))
  \<box>
  ((internal__GasAnalysis_Chemical.(NID_NoGas_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> Skip);; (enter_Reading_GasAnalysis_Chemical \<rightarrow> Skip))))))
  \<box>
  ((sts = noGas) & (((internal__GasAnalysis_Chemical.(NID_Analysis_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> (SSTOP \<triangle> (resume_out \<rightarrow> Skip)));; (enter_NoGas_GasAnalysis_Chemical \<rightarrow> Skip))))))))
  \<box>
  ((sts = gasD) & (((internal__GasAnalysis_Chemical.(NID_Analysis_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> Skip);; (enter_GasDetected_GasAnalysis_Chemical \<rightarrow> Skip))))))))
  \<box>
  (goreq(ins,thr) & (((internal__GasAnalysis_Chemical.(NID_GasDetected_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> (SSTOP \<triangle> (stop_out \<rightarrow> Skip)));; (enter_j1_GasAnalysis_Chemical \<rightarrow> Skip))))))))
  \<box>
  ((\<not>goreq(ins,thr)) & (((internal__GasAnalysis_Chemical.(NID_GasDetected_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> ((SSTOP \<triangle> (get_gs?(gs) \<rightarrow> (SSTOP \<triangle> (set_anl!location(gs) \<rightarrow> Skip))));; (SSTOP \<triangle> (get_anl?(anl) \<rightarrow> (SSTOP \<triangle> (turn_out!anl \<rightarrow> Skip))))));; (enter_Reading_GasAnalysis_Chemical \<rightarrow> Skip))))))))
  \<box>
  (share \<rightarrow> Skip));; prefixedTransAction_GasAnalysis_Chemical)
  \<box>
  (((interrupt_GasAnalysis_Chemical \<rightarrow> (SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_GasAnalysis_Chemical \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip)))))))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess prefixedTransAction_GasAnalysis_Chemical"

end

locale ncBehaviourProc_GasAnalysis_Chemical
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
" ncBehaviourProc_GasAnalysis_Chemical = 
	(((((((((((node_proc_j1_GasAnalysis_Chemical \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> node_proc_Analysis_GasAnalysis_Chemical) \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> node_proc_Reading_GasAnalysis_Chemical) \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> node_proc_GasDetected_GasAnalysis_Chemical) \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> node_proc_i1_GasAnalysis_Chemical) \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> node_proc_NoGas_GasAnalysis_Chemical)
	  [ interrupt_i1_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_i1_GasAnalysis_Chemical,  
	 interrupt_Reading_GasAnalysis_Chemical \<mapsto> gas__in\<cdot>NID_Reading_GasAnalysis_Chemical,  
	 interrupt_NoGas_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_NoGas_GasAnalysis_Chemical,  
	 interrupt_Analysis_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_Analysis_GasAnalysis_Chemical,  
	 interrupt_Analysis_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_Analysis_GasAnalysis_Chemical,  
	 interrupt_GasDetected_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_GasDetected_GasAnalysis_Chemical,  
	 interrupt_GasDetected_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_GasDetected_GasAnalysis_Chemical,  
	 interrupt_j1_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical,  
	 interrupt_NoGas_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical,  
	 interrupt_Reading_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical,  
	 interrupt_GasDetected_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical,  
	 interrupt_Analysis_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical ])
	  [ share \<mapsto> share,  
	 set_sts \<mapsto> setL_sts,  
	 set_ins \<mapsto> setL_ins ]) \<lbrakk> | parallel_chanset_ncCoreBeh_GasAnalysis_Chemical | \<rbrakk> (trans_proc_GasAnalysis_Chemical
	  [ share \<mapsto> share,  
	 share \<mapsto> setL_sts,  
	 share \<mapsto> setL_ins ]))
	  [ setL_sts \<mapsto> set_sts,  
	 setL_ins \<mapsto> set_ins ]) \<Zhide> ncCoreBeh_hideset_GasAnalysis_Chemical)
	  [ gas__in\<cdot>x \<mapsto> gas_in ]) "

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess ncBehaviourProc_GasAnalysis_Chemical.ProcDef"

end
 
end





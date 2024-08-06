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


\<comment> \<open>constant and function declaration\<close>
consts intensity :: "(GasSensor list) \<RightArrow> Intensity"

consts angle :: "nat \<RightArrow> Angle"

consts location :: "(GasSensor list) \<RightArrow> Angle"

consts analysis :: "(GasSensor list) \<RightArrow> Status"

consts goreq :: "Intensity\<times>Intensity \<RightArrow> boolean"

consts thr_GasAnalysis_Chemical :: "Intensity"

consts thr_GasAnalysis_Chemical :: "Intensity"


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

get_sts_GasAnalysis_Chemical :: "Status"
set_sts_GasAnalysis_Chemical :: "Status"
setL_sts_GasAnalysis_Chemical :: "Status"
setR_sts_GasAnalysis_Chemical :: "Status"

get_gs_GasAnalysis_Chemical :: "(GasSensor list)"
set_gs_GasAnalysis_Chemical :: "(GasSensor list)"
setL_gs_GasAnalysis_Chemical :: "(GasSensor list)"
setR_gs_GasAnalysis_Chemical :: "(GasSensor list)"

get_ins_GasAnalysis_Chemical :: "Intensity"
set_ins_GasAnalysis_Chemical :: "Intensity"
setL_ins_GasAnalysis_Chemical :: "Intensity"
setR_ins_GasAnalysis_Chemical :: "Intensity"

get_anl_GasAnalysis_Chemical :: "Angle"
set_anl_GasAnalysis_Chemical :: "Angle"
setL_anl_GasAnalysis_Chemical :: "Angle"
setR_anl_GasAnalysis_Chemical :: "Angle"
	
\<comment> \<open>shared_var_channel_GasAnalysis_Chemical\<close>
	
\<comment> \<open>event_channel_GasAnalysis_Chemical\<close>

gas_GasAnalysis_Chemical_in :: "(GasSensor list)"
gas_GasAnalysis_Chemical_out :: "(GasSensor list)"

resume_GasAnalysis_Chemical_in :: unit 
resume_GasAnalysis_Chemical_out :: unit 

turn_GasAnalysis_Chemical_in :: "Angle"
turn_GasAnalysis_Chemical_out :: "Angle"

stop_GasAnalysis_Chemical_in :: unit 
stop_GasAnalysis_Chemical_out :: unit 

gas_GasAnalysis_Chemical__in :: "NIDS_GasAnalysis_Chemical\<times>(GasSensor list)"

resume_GasAnalysis_Chemical__in :: "NIDS_GasAnalysis_Chemical"

turn_GasAnalysis_Chemical__in :: "NIDS_GasAnalysis_Chemical\<times>Angle"

stop_GasAnalysis_Chemical__in :: "NIDS_GasAnalysis_Chemical"
	
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
	  entered_NoGas_GasAnalysis_Chemical, 
	  entered_j1_GasAnalysis_Chemical, 
	  entered_Reading_GasAnalysis_Chemical, 
	  entered_Analysis_GasAnalysis_Chemical, 
	  entered_GasDetected_GasAnalysis_Chemical \<rbrace>"
	
definition "internal_events_GasAnalysis_Chemical = \<lbrace> 
	  enter_i1_GasAnalysis_Chemical, 
	  enter_GasDetected_GasAnalysis_Chemical, 
	  enter_j1_GasAnalysis_Chemical, 
	  enter_Reading_GasAnalysis_Chemical, 
	  enter_Analysis_GasAnalysis_Chemical, 
	  enter_NoGas_GasAnalysis_Chemical, 
	  entered_NoGas_GasAnalysis_Chemical, 
	  entered_j1_GasAnalysis_Chemical, 
	  entered_Reading_GasAnalysis_Chemical, 
	  entered_Analysis_GasAnalysis_Chemical, 
	  entered_GasDetected_GasAnalysis_Chemical, 
	  interrupt_GasAnalysis_Chemical, 
	  exited_GasAnalysis_Chemical \<rbrace>"
	
definition "sem__events_GasAnalysis_Chemical = \<lbrace> 
	  terminate, 
	  gas_GasAnalysis_Chemical_in, 
	  gas_GasAnalysis_Chemical_out, 
	  resume_GasAnalysis_Chemical_in, 
	  resume_GasAnalysis_Chemical_out, 
	  turn_GasAnalysis_Chemical_in, 
	  turn_GasAnalysis_Chemical_out, 
	  stop_GasAnalysis_Chemical_in, 
	  stop_GasAnalysis_Chemical_out \<rbrace>"
	
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
	  enter_Analysis_GasAnalysis_Chemical, 
	  interrupt_GasAnalysis_Chemical, 
	  setL_sts_GasAnalysis_Chemical, 
	  enter_i1_GasAnalysis_Chemical, 
	  internal__GasAnalysis_Chemical\<cdot>NID_NoGas_GasAnalysis_Chemical, 
	  enter_NoGas_GasAnalysis_Chemical, 
	  gas_GasAnalysis_Chemical__in\<cdot>NID_Reading_GasAnalysis_Chemical, 
	  enter_j1_GasAnalysis_Chemical, 
	  enter_Reading_GasAnalysis_Chemical, 
	  internal__GasAnalysis_Chemical\<cdot>NID_GasDetected_GasAnalysis_Chemical, 
	  exit_GasAnalysis_Chemical, 
	  share, 
	  terminate, 
	  setL_ins_GasAnalysis_Chemical \<rbrace>"

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
"Active = ((SSTOP \<triangle> (get_gs_GasAnalysis_Chemical?(gs_GasAnalysis_Chemical) \<rightarrow> ((size(gs) > 0) & ((SSTOP \<triangle> (set_ins_GasAnalysis_Chemical!intensity(gs_GasAnalysis_Chemical) \<rightarrow> Skip))))));; (Behaviour;; Exiting))" | 
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
"Active = (Skip;; (Behaviour;; Exiting))" | 
"Behaviour = (entered_Analysis_GasAnalysis_Chemical \<rightarrow> During)" | 
"During = (((SSTOP \<triangle> (get_gs_GasAnalysis_Chemical?(gs_GasAnalysis_Chemical) \<rightarrow> ((size(gs) > 0) & ((SSTOP \<triangle> (set_sts_GasAnalysis_Chemical!analysis(gs_GasAnalysis_Chemical) \<rightarrow> Skip))))));; SSTOP) \<triangle> (interrupt_Analysis_GasAnalysis_Chemical \<rightarrow> Skip))" | 
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
"prefixedTransAction_GasAnalysis_Chemical = (enter_i1_GasAnalysis_Chemical \<rightarrow> (SSTOP \<triangle> (get_sts_GasAnalysis_Chemical?(sts_GasAnalysis_Chemical) \<rightarrow> (get_ins_GasAnalysis_Chemical?(ins_GasAnalysis_Chemical) \<rightarrow> (((((((((((internal__GasAnalysis_Chemical.(NID_i1_GasAnalysis_Chemical) \<rightarrow> ((SSTOP \<triangle> (set_gs_GasAnalysis_Chemical![] \<rightarrow> Skip));; (SSTOP \<triangle> (set_anl_GasAnalysis_Chemical!Front \<rightarrow> Skip))));; (enter_Reading_GasAnalysis_Chemical \<rightarrow> Skip))
  \<box>
  ((gas_GasAnalysis_Chemical__in.(NID_Reading_GasAnalysis_Chemical)?(gs_GasAnalysis_Chemical) \<rightarrow> (SSTOP \<triangle> (set_gs_GasAnalysis_Chemical!gs_GasAnalysis_Chemical \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> Skip);; (enter_Analysis_GasAnalysis_Chemical \<rightarrow> Skip))))))
  \<box>
  ((internal__GasAnalysis_Chemical.(NID_NoGas_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> Skip);; (enter_Reading_GasAnalysis_Chemical \<rightarrow> Skip))))))
  \<box>
  ((sts_GasAnalysis_Chemical = noGas) & (((internal__GasAnalysis_Chemical.(NID_Analysis_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> (SSTOP \<triangle> (resume_GasAnalysis_Chemical_out \<rightarrow> Skip)));; (enter_NoGas_GasAnalysis_Chemical \<rightarrow> Skip))))))))
  \<box>
  ((sts_GasAnalysis_Chemical = gasD) & (((internal__GasAnalysis_Chemical.(NID_Analysis_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> Skip);; (enter_GasDetected_GasAnalysis_Chemical \<rightarrow> Skip))))))))
  \<box>
  (goreq(ins_GasAnalysis_Chemical,thr_GasAnalysis_Chemical) & (((internal__GasAnalysis_Chemical.(NID_GasDetected_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> (SSTOP \<triangle> (stop_GasAnalysis_Chemical_out \<rightarrow> Skip)));; (enter_j1_GasAnalysis_Chemical \<rightarrow> Skip))))))))
  \<box>
  ((\<not>goreq(ins_GasAnalysis_Chemical,thr_GasAnalysis_Chemical)) & (((internal__GasAnalysis_Chemical.(NID_GasDetected_GasAnalysis_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_Chemical \<rightarrow> ((SSTOP \<triangle> (get_gs_GasAnalysis_Chemical?(gs_GasAnalysis_Chemical) \<rightarrow> ((size(gs) > 0) & ((SSTOP \<triangle> (set_anl_GasAnalysis_Chemical!location(gs_GasAnalysis_Chemical) \<rightarrow> Skip))))));; (SSTOP \<triangle> (get_anl_GasAnalysis_Chemical?(anl_GasAnalysis_Chemical) \<rightarrow> (SSTOP \<triangle> (turn_GasAnalysis_Chemical_out!anl_GasAnalysis_Chemical \<rightarrow> Skip))))));; (enter_Reading_GasAnalysis_Chemical \<rightarrow> Skip))))))))
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
	 interrupt_Reading_GasAnalysis_Chemical \<mapsto> gas_GasAnalysis_Chemical__in\<cdot>NID_Reading_GasAnalysis_Chemical,  
	 interrupt_NoGas_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_NoGas_GasAnalysis_Chemical,  
	 interrupt_Analysis_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_Analysis_GasAnalysis_Chemical,  
	 interrupt_Analysis_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_Analysis_GasAnalysis_Chemical,  
	 interrupt_GasDetected_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_GasDetected_GasAnalysis_Chemical,  
	 interrupt_GasDetected_GasAnalysis_Chemical \<mapsto> internal__GasAnalysis_Chemical\<cdot>NID_GasDetected_GasAnalysis_Chemical,  
	 interrupt_NoGas_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical,  
	 interrupt_j1_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical,  
	 interrupt_Reading_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical,  
	 interrupt_Analysis_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical,  
	 interrupt_GasDetected_GasAnalysis_Chemical \<mapsto> interrupt_GasAnalysis_Chemical ])
	  [ share \<mapsto> share,  
	 set_sts_GasAnalysis_Chemical \<mapsto> setL_sts_GasAnalysis_Chemical,  
	 set_ins_GasAnalysis_Chemical \<mapsto> setL_ins_GasAnalysis_Chemical ]) \<lbrakk> | parallel_chanset_ncCoreBeh_GasAnalysis_Chemical | \<rbrakk> (trans_proc_GasAnalysis_Chemical
	  [ share \<mapsto> share,  
	 share \<mapsto> setL_sts_GasAnalysis_Chemical,  
	 share \<mapsto> setL_ins_GasAnalysis_Chemical ]))
	  [ setL_sts_GasAnalysis_Chemical \<mapsto> set_sts_GasAnalysis_Chemical,  
	 setL_ins_GasAnalysis_Chemical \<mapsto> set_ins_GasAnalysis_Chemical ]) \<Zhide> ncCoreBeh_hideset_GasAnalysis_Chemical)
	  [ gas_GasAnalysis_Chemical__in\<cdot>x \<mapsto> gas_GasAnalysis_Chemical_in ]) "

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess ncBehaviourProc_GasAnalysis_Chemical.ProcDef"

end
 
end





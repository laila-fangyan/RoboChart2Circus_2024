theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_GasAnalysis_stm_Chemical = 
	NID_i1_GasAnalysis_stm_Chemical | 
	NID_GasDetected_GasAnalysis_stm_Chemical | 
	NID_j1_GasAnalysis_stm_Chemical | 
	NID_Reading_GasAnalysis_stm_Chemical | 
	NID_Analysis_GasAnalysis_stm_Chemical | 
	NID_NoGas_GasAnalysis_stm_Chemical



\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>internal_channel_GasAnalysis_stm_Chemical\<close>

internal__GasAnalysis_stm_Chemical :: "NIDS_GasAnalysis_stm_Chemical"
	
\<comment> \<open>flowchannel_GasAnalysis_stm_Chemical\<close>

interrupt_GasAnalysis_stm_Chemical :: unit 
exited_GasAnalysis_stm_Chemical :: unit 
exit_GasAnalysis_stm_Chemical :: unit 
terminate :: unit 
	
\<comment> \<open>variable_channel_GasAnalysis_stm_Chemical\<close>

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
	
\<comment> \<open>event_channel_GasAnalysis_stm_Chemical\<close>

gas_in :: "(GasSensor list)"
gas_out :: "(GasSensor list)"

resume_in :: unit 
resume_out :: unit 

turn_in :: "Angle"
turn_out :: "Angle"

stop_in :: unit 
stop_out :: unit 

gas__in :: "NIDS_GasAnalysis_stm_Chemical\<times>(GasSensor list)"

resume__in :: "NIDS_GasAnalysis_stm_Chemical"

turn__in :: "NIDS_GasAnalysis_stm_Chemical\<times>Angle"

stop__in :: "NIDS_GasAnalysis_stm_Chemical"
	
\<comment> \<open>junction_channel_i1_GasAnalysis_stm_Chemical\<close>

enter_i1_GasAnalysis_stm_Chemical :: unit 
interrupt_i1_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_GasDetected_GasAnalysis_stm_Chemical\<close>

enter_GasDetected_GasAnalysis_stm_Chemical :: unit 
entered_GasDetected_GasAnalysis_stm_Chemical :: unit 
interrupt_GasDetected_GasAnalysis_stm_Chemical :: unit 
enteredL_GasDetected_GasAnalysis_stm_Chemical :: unit 
enteredR_GasDetected_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_j1_GasAnalysis_stm_Chemical\<close>

enter_j1_GasAnalysis_stm_Chemical :: unit 
entered_j1_GasAnalysis_stm_Chemical :: unit 
interrupt_j1_GasAnalysis_stm_Chemical :: unit 
enteredL_j1_GasAnalysis_stm_Chemical :: unit 
enteredR_j1_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_Reading_GasAnalysis_stm_Chemical\<close>

enter_Reading_GasAnalysis_stm_Chemical :: unit 
entered_Reading_GasAnalysis_stm_Chemical :: unit 
interrupt_Reading_GasAnalysis_stm_Chemical :: unit 
enteredL_Reading_GasAnalysis_stm_Chemical :: unit 
enteredR_Reading_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_Analysis_GasAnalysis_stm_Chemical\<close>

enter_Analysis_GasAnalysis_stm_Chemical :: unit 
entered_Analysis_GasAnalysis_stm_Chemical :: unit 
interrupt_Analysis_GasAnalysis_stm_Chemical :: unit 
enteredL_Analysis_GasAnalysis_stm_Chemical :: unit 
enteredR_Analysis_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_NoGas_GasAnalysis_stm_Chemical\<close>

enter_NoGas_GasAnalysis_stm_Chemical :: unit 
entered_NoGas_GasAnalysis_stm_Chemical :: unit 
interrupt_NoGas_GasAnalysis_stm_Chemical :: unit 
enteredL_NoGas_GasAnalysis_stm_Chemical :: unit 
enteredR_NoGas_GasAnalysis_stm_Chemical :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_GasAnalysis_stm_Chemical = \<lbrace> 
	  enter_i1_GasAnalysis_stm_Chemical, 
	  enter_GasDetected_GasAnalysis_stm_Chemical, 
	  enter_j1_GasAnalysis_stm_Chemical, 
	  enter_Reading_GasAnalysis_stm_Chemical, 
	  enter_Analysis_GasAnalysis_stm_Chemical, 
	  enter_NoGas_GasAnalysis_stm_Chemical \<rbrace>"
	
definition "enteredSS_GasAnalysis_stm_Chemical = \<lbrace> 
	  entered_Analysis_GasAnalysis_stm_Chemical, 
	  entered_j1_GasAnalysis_stm_Chemical, 
	  entered_GasDetected_GasAnalysis_stm_Chemical, 
	  entered_NoGas_GasAnalysis_stm_Chemical, 
	  entered_Reading_GasAnalysis_stm_Chemical \<rbrace>"
	
definition "internal_events_GasAnalysis_stm_Chemical = \<lbrace> 
	  enter_i1_GasAnalysis_stm_Chemical, 
	  enter_GasDetected_GasAnalysis_stm_Chemical, 
	  enter_j1_GasAnalysis_stm_Chemical, 
	  enter_Reading_GasAnalysis_stm_Chemical, 
	  enter_Analysis_GasAnalysis_stm_Chemical, 
	  enter_NoGas_GasAnalysis_stm_Chemical, 
	  entered_Analysis_GasAnalysis_stm_Chemical, 
	  entered_j1_GasAnalysis_stm_Chemical, 
	  entered_GasDetected_GasAnalysis_stm_Chemical, 
	  entered_NoGas_GasAnalysis_stm_Chemical, 
	  entered_Reading_GasAnalysis_stm_Chemical, 
	  interrupt_GasAnalysis_stm_Chemical, 
	  exited_GasAnalysis_stm_Chemical \<rbrace>"
	
definition "shared_variable_events_GasAnalysis_stm_Chemical = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_GasAnalysis_stm_Chemical = \<lbrace> 
	  terminate, 
	  gas_in, 
	  gas_out, 
	  resume_in, 
	  resume_out, 
	  turn_in, 
	  turn_out, 
	  stop_in, 
	  stop_out \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
	"relu x = max 0 x"
 
end





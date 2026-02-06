
theory circus_HOLCSP 
	imports "RC_HOL-CSP.RoboChart_Library"
begin

subsection \<open> Model \<close>


	
	
datatype NIDS_stm3_ex2 = 
	NID_i0_stm3_ex2 | 
	NID_f0_stm3_ex2 | 
	NID_s0_stm3_ex2 | 
	NID_s1_stm3_ex2 
instantiation NIDS_stm3_ex2 :: discrete_cpo
begin

definition below_NIDS_stm3_ex2_def:
  "(x::NIDS_stm3_ex2) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_stm3_ex2_def)

end
 




\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_stm3_ex2\<close>

"internal__stm3_ex2" "NIDS_stm3_ex2"  |	
\<comment> \<open>flowchannel_stmbd_stm3_ex2\<close>

"interrupt_stm3_ex2"  |"exited_stm3_ex2"  |"exit_stm3_ex2"  |	
\<comment> \<open>var_channel_stmbd_stm3_ex2\<close>

"get_v1" "int"  |"set_v1" "int"  |"setL_v1" "int"  |"setR_v1" "int"  |
"get_v" "int"  |"set_v" "int"  |"setL_v" "int"  |"setR_v" "int"  |	
\<comment> \<open>event_channel_stmbd_stm3_ex2\<close>

"a_in"  |"a_out"  |
"b_in"  |"b_out"  |
"a__in" "NIDS_stm3_ex2"  |
"b__in" "NIDS_stm3_ex2"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm3_ex2\<close>

"enter_i0_stm3_ex2"  |"interrupt_i0_stm3_ex2"  |	
\<comment> \<open>state_channel_in_stmbd_f0_stm3_ex2\<close>

"enter_f0_stm3_ex2"  |"entered_f0_stm3_ex2"  |"interrupt_f0_stm3_ex2"  |"enteredL_f0_stm3_ex2"  |"enteredR_f0_stm3_ex2"  |	
\<comment> \<open>state_channel_in_stmbd_s0_stm3_ex2\<close>

"enter_s0_stm3_ex2"  |"entered_s0_stm3_ex2"  |"interrupt_s0_stm3_ex2"  |"enteredL_s0_stm3_ex2"  |"enteredR_s0_stm3_ex2"  |	
\<comment> \<open>state_channel_in_stmbd_s1_stm3_ex2\<close>

"enter_s1_stm3_ex2"  |"entered_s1_stm3_ex2"  |"interrupt_s1_stm3_ex2"  |"enteredL_s1_stm3_ex2"  |"enteredR_s1_stm3_ex2"  |	
\<comment> \<open>assumption-guarantee_viol_stm3_ex2\<close>

"aviol"  |"gviol" 	

\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_stm3_ex2 = 	{  enter_i0_stm3_ex2, 
 enter_f0_stm3_ex2, 
 enter_s0_stm3_ex2, 
 enter_s1_stm3_ex2 }"
	
definition "enteredSS_in_stmbd_stm3_ex2 = 	{  entered_s1_stm3_ex2, 
 entered_s0_stm3_ex2, 
 entered_f0_stm3_ex2 }"
	
definition "internal_events_in_stmbd_stm3_ex2 = 	{  enter_i0_stm3_ex2, 
 enter_f0_stm3_ex2, 
 enter_s0_stm3_ex2, 
 enter_s1_stm3_ex2, 
 entered_s1_stm3_ex2, 
 entered_s0_stm3_ex2, 
 entered_f0_stm3_ex2, 
 interrupt_stm3_ex2, 
 exited_stm3_ex2 }"
	
definition "shared_variable_events_in_stmbd_stm3_ex2 = {}	
definition "sem__events_stm_stm3_ex2 = 	{  terminate, 
 a_in, 
 a_out, 
 b_in, 
 b_out }"

      
abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"
abbreviation "SSTOP \<equiv> SSTOP_aux share"  

          


 

locale Trans 
begin
fixrec Trans_stm3_ex2 :: "NIDS_stm3_ex2 \<rightarrow> chan_event process"
where
[simp del] :\<open>Trans_stm3_ex2\<cdot>n = 
	((SSTOP \<triangle> (get_v\<^bold>?v \<rightarrow> (get_v1\<^bold>?v1 \<rightarrow> (assume True (Trans_stm3_ex2\<cdot>n) ((((((((n = NID_i0_stm3_ex2) \<^bold>& (((internal__stm3_ex2\<^bold>.NID_i0_stm3_ex2 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3_ex2 \<rightarrow> Trans_stm3_ex2\<cdot>NID_s0_stm3_ex2))))
	  \<box>
	  ((n = NID_s0_stm3_ex2) \<^bold>& ((((v1 \<ge> 1)) \<^bold>& (((internal__stm3_ex2\<^bold>.NID_s0_stm3_ex2 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3_ex2 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm3_ex2 \<rightarrow> Trans_stm3_ex2\<cdot>NID_s1_stm3_ex2))))))))))
	  \<box>
	  ((n = NID_s1_stm3_ex2) \<^bold>& ((((v1 < 1)) \<^bold>& (((internal__stm3_ex2\<^bold>.NID_s1_stm3_ex2 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3_ex2 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3_ex2 \<rightarrow> Trans_stm3_ex2\<cdot>NID_s0_stm3_ex2))))))))))
	  \<box>
	  ((n = NID_s1_stm3_ex2) \<^bold>& (((a__in\<^bold>.NID_s1_stm3_ex2 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3_ex2 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm3_ex2 \<rightarrow> Trans_stm3_ex2\<cdot>NID_s0_stm3_ex2))))))))
	  \<box>
	  ((n = NID_s1_stm3_ex2) \<^bold>& ((((v > 3)) \<^bold>& (((internal__stm3_ex2\<^bold>.NID_s1_stm3_ex2 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm3_ex2 \<rightarrow> Skip)\<^bold>;  (enter_f0_stm3_ex2 \<rightarrow> Trans_stm3_ex2\<cdot>NID_f0_stm3_ex2))))))))))
	  \<box>
	  (share \<rightarrow> Trans_stm3_ex2\<cdot>n))
	  \<box>
	  (((interrupt_stm3_ex2 \<rightarrow> (SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm3_ex2 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))))))) \<close>
end
abbreviation "InactiveJct_i0_stm3_ex2 \<equiv> RC_Junction.Inactive share enter_i0_stm3_ex2 interrupt_i0_stm3_ex2 terminate" 



abbreviation "InactiveFn_f0_stm3_ex2 \<equiv> RC_FinalState.Inactive share enter_f0_stm3_ex2 entered_f0_stm3_ex2 interrupt_f0_stm3_ex2 exit_stm3_ex2 exited_stm3_ex2 terminate"



abbreviation "Inactive_s0_stm3_ex2 \<equiv> RC_SimpleState.Inactive share enter_s0_stm3_ex2 entered_s0_stm3_ex2 interrupt_s0_stm3_ex2 exit_stm3_ex2 exited_stm3_ex2 terminate (SSTOP \<triangle> (b_out \<rightarrow> Skip)) Skip Skip"


abbreviation "Inactive_s1_stm3_ex2 \<equiv> RC_SimpleState.Inactive share enter_s1_stm3_ex2 entered_s1_stm3_ex2 interrupt_s1_stm3_ex2 exit_stm3_ex2 exited_stm3_ex2 terminate Skip Skip (SSTOP \<triangle> (get_v\<^bold>?v \<rightarrow> (assume True (Trans_tbd\<cdot>n) (SSTOP \<triangle> (guar True (set_v\<^bold>!(v + 1) \<rightarrow> Skip))))))"

abbreviation "composeNodes_stm3_ex2 \<equiv> RC_CompNodes.composeNodes share terminate [InactiveJct_i0_stm3_ex2,InactiveFn_f0_stm3_ex2,Inactive_s0_stm3_ex2,Inactive_s1_stm3_ex2]"

abbreviation "Memory_v1_stm3_ex2 \<equiv> RC_Memory.Mem get_v1_stm3_ex2 set_v1_stm3_ex2 terminate"
abbreviation "Memory_v_stm3_ex2 \<equiv> RC_Memory.Mem get_v_stm3_ex2 set_v_stm3_ex2 terminate"





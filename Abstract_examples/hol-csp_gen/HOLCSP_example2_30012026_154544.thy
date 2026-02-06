
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


definition "enteredSS_in_stmbd_stm3_ex2 = 	{  entered_s0_stm3_ex2, 
 entered_s1_stm3_ex2, 
 entered_f0_stm3_ex2 }"


definition "internal_events_in_stmbd_stm3_ex2 = 	{  enter_i0_stm3_ex2, 
 enter_f0_stm3_ex2, 
 enter_s0_stm3_ex2, 
 enter_s1_stm3_ex2, 
 entered_s0_stm3_ex2, 
 entered_s1_stm3_ex2, 
 entered_f0_stm3_ex2, 
 interrupt_stm3_ex2, 
 exited_stm3_ex2 }"


definition "shared_variable_events_in_stmbd_stm3_ex2 = {}"

definition "sem__events_stm_stm3_ex2 = 	{  terminate, 
 a_in, 
 a_out, 
 b_in, 
 b_out }"
      
abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"
abbreviation "SSTOP \<equiv> SSTOP_aux share"  

          


 

locale actions 
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

fixrec
InactiveJct_i0_stm3_ex2 :: "chan_event process" and 
Activation_i0_stm3_ex2 :: "chan_event process" and 
Termination_i0_stm3_ex2 :: "chan_event process" and 
Active_i0_stm3_ex2 :: "chan_event process" and 
InactiveFn_f0_stm3_ex2 :: "chan_event process" and 
Activation_f0_stm3_ex2 :: "chan_event process" and 
Termination_f0_stm3_ex2 :: "chan_event process" and 
Entering_f0_stm3_ex2 :: "chan_event process" and 
Active_f0_stm3_ex2 :: "chan_event process" and 
Interrupted_f0_stm3_ex2 :: "chan_event process" and 
Inactive_s0_stm3_ex2 :: "chan_event process" and 
Activation_s0_stm3_ex2 :: "chan_event process" and 
Termination_s0_stm3_ex2 :: "chan_event process" and 
Active_s0_stm3_ex2 :: "chan_event process" and 
Behaviour_s0_stm3_ex2 :: "chan_event process" and 
During_s0_stm3_ex2 :: "chan_event process" and 
Exiting_s0_stm3_ex2 :: "chan_event process" and 
Inactive_s1_stm3_ex2 :: "chan_event process" and 
Activation_s1_stm3_ex2 :: "chan_event process" and 
Termination_s1_stm3_ex2 :: "chan_event process" and 
Active_s1_stm3_ex2 :: "chan_event process" and 
Behaviour_s1_stm3_ex2 :: "chan_event process" and 
During_s1_stm3_ex2 :: "chan_event process" and 
Exiting_s1_stm3_ex2 :: "chan_event process"
where
[simp del] :\<open>InactiveJct_i0_stm3_ex2 = 
	(SSTOP \<triangle> (Activation_i0_stm3_ex2
	  \<box>
	  Termination_i0_stm3_ex2)) \<close>  | 	
[simp del] :\<open>Activation_i0_stm3_ex2 = 
	(enter_i0_stm3_ex2 \<rightarrow> Active_i0_stm3_ex2) \<close>  | 	
[simp del] :\<open>Termination_i0_stm3_ex2 = 
	(terminate \<rightarrow> Skip) \<close>  | 	
[simp del] :\<open>Active_i0_stm3_ex2 = 
	((SSTOP \<triangle> (interrupt_i0_stm3_ex2 \<rightarrow> Skip))\<^bold>;  InactiveJct_i0_stm3_ex2) \<close>  | 	
[simp del] :\<open>InactiveFn_f0_stm3_ex2 = 
	(SSTOP \<triangle> (Activation_f0_stm3_ex2
	  \<box>
	  Termination_f0_stm3_ex2)) \<close>  | 	
[simp del] :\<open>Activation_f0_stm3_ex2 = 
	(enter_f0_stm3_ex2 \<rightarrow> Entering_f0_stm3_ex2) \<close>  | 	
[simp del] :\<open>Termination_f0_stm3_ex2 = 
	(terminate \<rightarrow> Skip) \<close>  | 	
[simp del] :\<open>Entering_f0_stm3_ex2 = 
	(entered_f0_stm3_ex2 \<rightarrow> Active_f0_stm3_ex2) \<close>  | 	
[simp del] :\<open>Active_f0_stm3_ex2 = 
	(SSTOP \<triangle> (Termination_f0_stm3_ex2
	  \<box>
	  (interrupt_f0_stm3_ex2 \<rightarrow> Interrupted_f0_stm3_ex2))) \<close>  | 	
[simp del] :\<open>Interrupted_f0_stm3_ex2 = 
	(SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> (exited_stm3_ex2 \<rightarrow> InactiveFn_f0_stm3_ex2))) \<close>  | 	
[simp del] :\<open>Inactive_s0_stm3_ex2 = 
	(SSTOP \<triangle> (Activation_s0_stm3_ex2
	  \<box>
	  Termination_s0_stm3_ex2)) \<close>  | 	
[simp del] :\<open>Activation_s0_stm3_ex2 = 
	(enter_s0_stm3_ex2 \<rightarrow> Active_s0_stm3_ex2) \<close>  | 	
[simp del] :\<open>Termination_s0_stm3_ex2 = 
	(terminate \<rightarrow> Skip) \<close>  | 	
[simp del] :\<open>Active_s0_stm3_ex2 = 
	((SSTOP \<triangle> (b_out \<rightarrow> Skip))\<^bold>;  (Behaviour_s0_stm3_ex2\<^bold>;  Exiting_s0_stm3_ex2)) \<close>  | 	
[simp del] :\<open>Behaviour_s0_stm3_ex2 = 
	(entered_s0_stm3_ex2 \<rightarrow> During_s0_stm3_ex2) \<close>  | 	
[simp del] :\<open>During_s0_stm3_ex2 = 
	((Skip\<^bold>;  SSTOP) \<triangle> (interrupt_s0_stm3_ex2 \<rightarrow> Skip)) \<close>  | 	
[simp del] :\<open>Exiting_s0_stm3_ex2 = 
	((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip))\<^bold>;  (Skip\<^bold>;  (exited_stm3_ex2 \<rightarrow> Inactive_s0_stm3_ex2))) \<close>  | 	
[simp del] :\<open>Inactive_s1_stm3_ex2 = 
	(SSTOP \<triangle> (Activation_s1_stm3_ex2
	  \<box>
	  Termination_s1_stm3_ex2)) \<close>  | 	
[simp del] :\<open>Activation_s1_stm3_ex2 = 
	(enter_s1_stm3_ex2 \<rightarrow> Active_s1_stm3_ex2) \<close>  | 	
[simp del] :\<open>Termination_s1_stm3_ex2 = 
	(terminate \<rightarrow> Skip) \<close>  | 	
[simp del] :\<open>Active_s1_stm3_ex2 = 
	(Skip\<^bold>;  (Behaviour_s1_stm3_ex2\<^bold>;  Exiting_s1_stm3_ex2)) \<close>  | 	
[simp del] :\<open>Behaviour_s1_stm3_ex2 = 
	(entered_s1_stm3_ex2 \<rightarrow> During_s1_stm3_ex2) \<close>  | 	
[simp del] :\<open>During_s1_stm3_ex2 = 
	((Skip\<^bold>;  SSTOP) \<triangle> (interrupt_s1_stm3_ex2 \<rightarrow> Skip)) \<close>  | 	
[simp del] :\<open>Exiting_s1_stm3_ex2 = 
	((SSTOP \<triangle> (exit_stm3_ex2 \<rightarrow> Skip))\<^bold>;  ((SSTOP \<triangle> (get_v\<^bold>?v \<rightarrow> (assume True (Trans_tbd\<cdot>n) (SSTOP \<triangle> (guar True (set_v\<^bold>!(v + 1) \<rightarrow> Skip))))))\<^bold>;  (exited_stm3_ex2 \<rightarrow> Inactive_s1_stm3_ex2))) \<close> 	

fixrec composeNodes_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>composeNodes_stm3_ex2 = 
	(((InactiveJct_i0_stm3_ex2
	  \<lbrakk> { share,terminate } \<rbrakk> 
	  InactiveFn_f0_stm3_ex2)
	  \<lbrakk> { share,terminate } \<rbrakk> 
	  Inactive_s0_stm3_ex2)
	  \<lbrakk> { share,terminate } \<rbrakk> 
	  Inactive_s1_stm3_ex2) \<close> 

fixrec ncCoreBehaviour_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>ncCoreBehaviour_stm3_ex2 = 
	((((composeNodes_stm3_ex2 \<lbrakk> interrupt_i0_stm3_ex2 := internal__stm3_ex2\<cdot>NID_i0_stm3_ex2,  
	 interrupt_s0_stm3_ex2 := internal__stm3_ex2\<cdot>NID_s0_stm3_ex2,  
	 interrupt_s1_stm3_ex2 := internal__stm3_ex2\<cdot>NID_s1_stm3_ex2,  
	 interrupt_s1_stm3_ex2 := a__in\<cdot>NID_s1_stm3_ex2,  
	 interrupt_s1_stm3_ex2 := internal__stm3_ex2\<cdot>NID_s1_stm3_ex2,  
	 interrupt_s0_stm3_ex2 := interrupt_stm3_ex2,  
	 interrupt_s1_stm3_ex2 := interrupt_stm3_ex2,  
	 interrupt_f0_stm3_ex2 := interrupt_stm3_ex2 \<rbrakk> \<lbrakk>\<rbrakk>) \<lbrakk> share := share,  
	 set_v := setL_v \<rbrakk> \<lbrakk>\<rbrakk>)
	  \<lbrakk> { exited_stm3_ex2,enter_s0_stm3_ex2,setL_v,enter_s1_stm3_ex2,enter_i0_stm3_ex2,internal__stm3_ex2\<cdot>NID_i0_stm3_ex2,internal__stm3_ex2\<cdot>NID_s1_stm3_ex2,exit_stm3_ex2,a__in\<cdot>NID_s1_stm3_ex2,internal__stm3_ex2\<cdot>NID_s0_stm3_ex2,enter_f0_stm3_ex2,interrupt_stm3_ex2,share,terminate } \<rbrakk> 
	  ((enter_i0_stm3_ex2 \<rightarrow> Trans_stm3_ex2) \<lbrakk> share := share,  
	 share := setL_v \<rbrakk> \<lbrakk>\<rbrakk>)) \<lbrakk> setL_v := set_v \<rbrakk> \<lbrakk>\<rbrakk>) \<close> 

fixrec ncBehaviour_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>ncBehaviour_stm3_ex2 = 
	((ncCoreBehaviour_stm3_ex2 \{ enter_i0_stm3_ex2,enter_f0_stm3_ex2,enter_s0_stm3_ex2,enter_s1_stm3_ex2,exit_stm3_ex2,exited_stm3_ex2,internal__stm3_ex2 }) \<lbrakk> a__in\<cdot>x := a_in \<rbrakk> \<lbrakk>\<rbrakk>) \<close> 

fixrec machineBody_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>machineBody_stm3_ex2 = 
	((ncBehaviour_stm3_ex2
	  \<lbrakk> { interrupt_stm3_ex2 } \<rbrakk> 
	  Skip) \{ enteredSS_stm3_ex2 }) \<close> 

fixrec Memory_v1_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>Memory_v1_stm3_ex2 = 
	(((get_v1_stm3_ex2\<^bold>!value \<rightarrow> Memory_v1_stm3_ex2\<cdot>value)
	  \<box>
	  ((set_v1_stm3_ex2\<^bold>?x__ \<rightarrow> Memory_v1_stm3_ex2\<cdot>x__)
	  \<box>
	  (terminate \<rightarrow> Skip)))) \<close> 

fixrec Memory_v_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>Memory_v_stm3_ex2 = 
	(((get_v_stm3_ex2\<^bold>!value \<rightarrow> Memory_v_stm3_ex2\<cdot>value)
	  \<box>
	  ((set_v_stm3_ex2\<^bold>?x__ \<rightarrow> Memory_v_stm3_ex2\<cdot>x__)
	  \<box>
	  (terminate \<rightarrow> Skip)))) \<close> 

fixrec varMemory_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>varMemory_stm3_ex2 = 
	(Memory_v1_stm3_ex2\<cdot>0
	  \<lbrakk> { terminate } \<rbrakk> 
	  Memory_v_stm3_ex2\<cdot>0) \<close> 

fixrec stateful_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>stateful_stm3_ex2 = 
	((machineBody_stm3_ex2
	  \<lbrakk> { get_v,set_v1,terminate,get_v1,set_v } \<rbrakk> 
	  varMemory_stm3_ex2) \{ get_v,set_v1,terminate,get_v1,set_v }) \<close> 

fixrec sharedVarMemory_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>sharedVarMemory_stm3_ex2 = 
	(terminate \<rightarrow> Skip) \<close> 

fixrec stm_stm3_ex2 :: "chan_event process"
where 
[simp del] :\<open>stm_stm3_ex2 = 
	((((((stateful_stm3_ex2 \{ terminate })\<^bold>;  (SSTOP \<triangle> (terminate \<rightarrow> Skip))) \<lbrakk>  \<rbrakk> \<lbrakk>\<rbrakk>)
	  \<lbrakk> { shared } \<rbrakk> 
	  Skip)
	  \<lbrakk> { terminate } \<rbrakk> 
	  sharedVarMemory_stm3_ex2) \{  }) \<close> 

end



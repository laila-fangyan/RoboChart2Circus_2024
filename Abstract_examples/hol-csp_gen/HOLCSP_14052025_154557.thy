
theory circus_HOLCSP 
	imports DeadlockFreedom
begin

subsection \<open> Model \<close>


	
	
datatype NIDS_stm04 = 
	NID_i0_stm04 | 
	NID_s0_stm04 | 
	NID_s1_stm04 
instantiation NIDS_stm04 :: discrete_cpo
begin

definition below_NIDS_stm04_def:
  "(x::NIDS_stm04) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_stm04_def)

end
 




\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_stm04\<close>

"internal__stm04" "NIDS_stm04"  |	
\<comment> \<open>flowchannel_stmbd_stm04\<close>

"interrupt_stm04"  |"exited_stm04"  |"exit_stm04"  |	
\<comment> \<open>var_channel_stmbd_stm04\<close>

"get_v1" "int"  |"set_v1" "int"  |"setL_v1" "int"  |"setR_v1" "int"  |
"get_bl" "bool"  |"set_bl" "bool"  |"setL_bl" "bool"  |"setR_bl" "bool"  |	
\<comment> \<open>event_channel_stmbd_stm04\<close>

"a_in"  |"a_out"  |
"b_in"  |"b_out"  |
"c_in"  |"c_out"  |
"a__in" "NIDS_stm04"  |
"b__in" "NIDS_stm04"  |
"c__in" "NIDS_stm04"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm04\<close>

"enter_i0_stm04"  |"interrupt_i0_stm04"  |	
\<comment> \<open>state_channel_in_stmbd_s0_stm04\<close>

"enter_s0_stm04"  |"entered_s0_stm04"  |"interrupt_s0_stm04"  |"enteredL_s0_stm04"  |"enteredR_s0_stm04"  |	
\<comment> \<open>state_channel_in_stmbd_s1_stm04\<close>

"enter_s1_stm04"  |"entered_s1_stm04"  |"interrupt_s1_stm04"  |"enteredL_s1_stm04"  |"enteredR_s1_stm04"  |	
\<comment> \<open>assumption-guarantee_viol_stm04\<close>

"aviol"  |"gviol" 	

                              
 
locale Trans 
begin

abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"


fixrec  
  SSTOP       :: "chan_event process"              and
  Terminate   :: "chan_event process"              
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>

fixrec  
Trans_stm04 :: "NIDS_stm04 \<rightarrow> chan_event process"
where
[simp del] :\<open>Trans_stm04\<cdot>n = 
	((SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (assume True (Trans_stm04\<cdot>n) (((((((n = NID_i0_stm04) \<^bold>& (((internal__stm04\<^bold>.NID_i0_stm04 \<rightarrow> (assume True ((SSTOP \<triangle> (guar True (set_v1\<^bold>!1 \<rightarrow> Skip)))) (SSTOP \<triangle> (guar True (set_v1\<^bold>!1 \<rightarrow> Skip)))))\<^bold>;  (enter_s0_stm04 \<rightarrow> Trans_stm04\<cdot>NID_s0_stm04))))
	  \<box>
	  ((n = NID_s0_stm04) \<^bold>& ((((v1 \<ge> 1)) \<^bold>& (((internal__stm04\<^bold>.NID_s0_stm04 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm04 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm04 \<rightarrow> (SSTOP \<triangle> (get_bl\<^bold>?bl \<rightarrow> (assume True ((if (bl)then (assume True ((SSTOP \<triangle> (b_out \<rightarrow> Skip))) (SSTOP \<triangle> (b_out \<rightarrow> Skip))))else(assume True ((SSTOP \<triangle> (c_out \<rightarrow> Skip))) (SSTOP \<triangle> (c_out \<rightarrow> Skip)))) (if (bl)then (assume True ((SSTOP \<triangle> (b_out \<rightarrow> Skip))) (SSTOP \<triangle> (b_out \<rightarrow> Skip))))else(assume True ((SSTOP \<triangle> (c_out \<rightarrow> Skip))) (SSTOP \<triangle> (c_out \<rightarrow> Skip)))))))\<^bold>;  (enter_s1_stm04 \<rightarrow> Trans_stm04\<cdot>NID_s1_stm04))))))))))
	  \<box>
	  ((n = NID_s1_stm04) \<^bold>& ((((v1 < 1)) \<^bold>& (((internal__stm04\<^bold>.NID_s1_stm04 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm04 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm04 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm04 \<rightarrow> Trans_stm04\<cdot>NID_s0_stm04))))))))))
	  \<box>
	  ((n = NID_s1_stm04) \<^bold>& (((a__in\<^bold>.NID_s1_stm04 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm04 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm04 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm04 \<rightarrow> Trans_stm04\<cdot>NID_s0_stm04))))))))
	  \<box>
	  (share \<rightarrow> Trans_stm04\<cdot>n))
	  \<box>
	  (((interrupt_stm04 \<rightarrow> (SSTOP \<triangle> (exit_stm04 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm04 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))))))) \<close>

end
end




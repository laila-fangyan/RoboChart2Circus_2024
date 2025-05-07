theory circus_HOLCSP 
	imports DeadlockFreedom
begin

subsection \<open> Model \<close>


	
	
datatype NIDS_stm1 = 
	NID_i0_stm1 | 
	NID_s0_stm1 | 
	NID_s1_stm1 | 
	NID_f0_stm1 
instantiation NIDS_stm1 :: discrete_cpo
begin

definition below_NIDS_stm1_def:
  "(x::NIDS_stm1) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_stm1_def)

end
 




\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_stm1\<close>

"internal__stm1" "NIDS_stm1"  |	
\<comment> \<open>flowchannel_stmbd_stm1\<close>

"interrupt_stm1"  |"exited_stm1"  |"exit_stm1"  |	
\<comment> \<open>event_channel_stmbd_stm1\<close>

"a_in"  |"a_out"  |
"b_in"  |"b_out"  |
"c_in"  |"c_out"  |
"a__in" "NIDS_stm1"  |
"b__in" "NIDS_stm1"  |
"c__in" "NIDS_stm1"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm1\<close>

"enter_i0_stm1"  |"interrupt_i0_stm1"  |	
\<comment> \<open>state_channel_in_stmbd_s0_stm1\<close>

"enter_s0_stm1"  |"entered_s0_stm1"  |"interrupt_s0_stm1"  |"enteredL_s0_stm1"  |"enteredR_s0_stm1"  |	
\<comment> \<open>state_channel_in_stmbd_s1_stm1\<close>

"enter_s1_stm1"  |"entered_s1_stm1"  |"interrupt_s1_stm1"  |"enteredL_s1_stm1"  |"enteredR_s1_stm1"  |	
\<comment> \<open>state_channel_in_stmbd_f0_stm1\<close>

"enter_f0_stm1"  |"entered_f0_stm1"  |"interrupt_f0_stm1"  |"enteredL_f0_stm1"  |"enteredR_f0_stm1" 	

                              
 
locale Trans =
fixes d :: nat
begin

fixrec  
SSTOP       :: "chan_event process"              and
Terminate   :: "chan_event process"              and
 
Trans_stm1 :: "NIDS_stm1 \<rightarrow> chan_event process"
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>|
[simp del] :\<open>Trans_stm1\<cdot>n = 
	(((((((n_ \<^bold>& (((internal__stm1\<^bold>.NID_i0_stm1 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm1 \<rightarrow> Trans_stm1(s0_stm1)))))
	  \<box>
	  (n_ \<^bold>& (((a__in\<^bold>.NID_s0_stm1 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm1 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm1 \<rightarrow> Trans_stm1(s1_stm1)))))))))
	  \<box>
	  (n_ \<^bold>& (((b__in\<^bold>.NID_s1_stm1 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm1 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm1 \<rightarrow> Trans_stm1(s0_stm1)))))))))
	  \<box>
	  (n_ \<^bold>& (((internal__stm1\<^bold>.NID_s1_stm1 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm1 \<rightarrow> Skip)\<^bold>;  (enter_f0_stm1 \<rightarrow> Trans_stm1(f0_stm1)))))))))
	  \<box>
	  (share \<rightarrow> Trans_stm1(n)))
	  \<box>
	  (((interrupt_stm1 \<rightarrow> (SSTOP \<triangle> (exit_stm1 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm1 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))) \<close>

end
end




theory circus_HOLCSP 
	imports DeadlockFreedom
begin

subsection \<open> Model \<close>


	
	
datatype NIDS_stm4 = 
	NID_i0_stm4 | 
	NID_s0_stm4 | 
	NID_s1_stm4 
instantiation NIDS_stm4 :: discrete_cpo
begin

definition below_NIDS_stm4_def:
  "(x::NIDS_stm4) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_NIDS_stm4_def)

end
 




\<comment> \<open>Channel Declaration\<close>
datatype chan_event  = 
"share"|
\<comment> \<open>terminate_channel\<close>

"terminate"  |	
\<comment> \<open>internal_channel_stmbd_stm4\<close>

"internal__stm4" "NIDS_stm4"  |	
\<comment> \<open>flowchannel_stmbd_stm4\<close>

"interrupt_stm4"  |"exited_stm4"  |"exit_stm4"  |	
\<comment> \<open>var_channel_stmbd_stm4\<close>

"get_v1" "int"  |"set_v1" "int"  |"setL_v1" "int"  |"setR_v1" "int"  |	
\<comment> \<open>event_channel_stmbd_stm4\<close>

"a_in"  |"a_out"  |
"a__in" "NIDS_stm4"  |	
\<comment> \<open>junction_channel_in_stmbd_i0_stm4\<close>

"enter_i0_stm4"  |"interrupt_i0_stm4"  |	
\<comment> \<open>state_channel_in_stmbd_s0_stm4\<close>

"enter_s0_stm4"  |"entered_s0_stm4"  |"interrupt_s0_stm4"  |"enteredL_s0_stm4"  |"enteredR_s0_stm4"  |	
\<comment> \<open>state_channel_in_stmbd_s1_stm4\<close>

"enter_s1_stm4"  |"entered_s1_stm4"  |"interrupt_s1_stm4"  |"enteredL_s1_stm4"  |"enteredR_s1_stm4" 	

                              
 
locale Trans 
begin

fixrec 
  AVIOL       :: "chan_event process" where
  [simp del] :\<open>AVIOL = aviol \<rightarrow> AVIOL\<close>

abbreviation "assume b P \<equiv> (if b then P else AVIOL)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> STOP)"


fixrec  
SSTOP       :: "chan_event process"              and
Terminate   :: "chan_event process"              and
 
Trans_stm4 :: "NIDS_stm4 \<rightarrow> chan_event process"
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>|
[simp del] :\<open>Trans_stm4\<cdot>n = 
	((SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> (((((((n = i0) \<^bold>& (((internal__stm4\<^bold>.NID_i0_stm4 \<rightarrow> (SSTOP \<triangle> (set_v1\<^bold>!1 \<rightarrow> Skip)))\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4\<cdot>s0_stm4))))
	  \<box>
	  ((n = s0) \<^bold>& ((((v1 \<ge> 1)) \<^bold>& (((internal__stm4\<^bold>.NID_s0_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm4 \<rightarrow> Trans_stm4\<cdot>s1_stm4))))))))))
	  \<box>
	  ((n = s1) \<^bold>& ((((v1 < 1)) \<^bold>& (((internal__stm4\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4\<cdot>s0_stm4))))))))))
	  \<box>
	  ((n = s1) \<^bold>& (((a__in\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Trans_stm4\<cdot>s0_stm4))))))))
	  \<box>
	  (share \<rightarrow> Trans_stm4\<cdot>n))
	  \<box>
	  (((interrupt_stm4 \<rightarrow> (SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm4 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip)))))) \<close>

end
end




theory circus_HOLCSP 
	imports "HOLCF-Library.Nat_Discrete" "HOLCF-Library.Int_Discrete"
          "HOLCF-Library.List_Cpo"  DeadlockFreedom_Automation Law_Interrupt_Seq
begin

default_sort type


no_notation floor (\<open>\<lfloor>_\<rfloor>\<close>)
no_notation ceiling (\<open>\<lceil>_\<rceil>\<close>)

no_notation Cons  ("_ \<cdot>/ _" [66,65] 65)

abbreviation "dot"    :: "['a \<Rightarrow> 'b, 'a, 'b process] \<Rightarrow> 'b process"
  where      "dot c
 a P \<equiv> write c a P"

syntax   "_dot"  :: "[id, logic, 'a process] => 'a process"
                                        ("(3(_\<^bold>._) /\<rightarrow> _)" [0,0,78] 78)
translations
 
  "_dot c p P"     \<rightleftharpoons> "CONST dot c p P"


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

                              
 
locale Trans =
fixes d :: nat
begin

fixrec  
SSTOP       :: "chan_event process"              and
Terminate   :: "chan_event process"              and
 
Trans_stm4 :: "NIDS_stm4 \<rightarrow> chan_event process"
where
[simp del] :\<open>SSTOP = share \<rightarrow> SSTOP\<close>|
[simp del] :\<open>Terminate = terminate \<rightarrow> Terminate\<close>|
[simp del] :\<open>Trans_stm4\<cdot>n = 
	(SSTOP \<triangle> (get_v1\<^bold>?v1 \<rightarrow> ((((((((internal__stm4\<^bold>.NID_i0_stm4 \<rightarrow> (SSTOP \<triangle> (set_v1\<^bold>!1 \<rightarrow> Skip)))\<^bold>;  (enter_s0_stm4 \<rightarrow> Skip))
	  \<box>
	  ((v1 \<ge> 1) \<^bold>& (((internal__stm4\<^bold>.NID_s0_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s1_stm4 \<rightarrow> Skip))))))))
	  \<box>
	  ((v1 < 1) \<^bold>& (((internal__stm4\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Skip))))))))
	  \<box>
	  ((a__in\<^bold>.NID_s1_stm4 \<rightarrow> Skip)\<^bold>;  ((SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip))\<^bold>;  (SSTOP \<triangle> ((exited_stm4 \<rightarrow> Skip)\<^bold>;  (enter_s0_stm4 \<rightarrow> Skip))))))
	  \<box>
	  (share \<rightarrow> Skip))\<^bold>;  Trans_stm4)
	  \<box>
	  (((interrupt_stm4 \<rightarrow> (SSTOP \<triangle> (exit_stm4 \<rightarrow> Skip)))\<^bold>;  (SSTOP \<triangle> (exited_stm4 \<rightarrow> (terminate \<rightarrow> Skip))))
	  \<box>
	  (terminate \<rightarrow> Skip))))) \<close>

end
end




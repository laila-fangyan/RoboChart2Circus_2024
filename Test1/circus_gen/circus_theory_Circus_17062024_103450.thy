theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>



\<comment> \<open>Channel Decleration\<close>
chantype mychan = 
share :: unit


\<comment> \<open>ChannelSet Decleration\<close>

definition relu :: "real \<Rightarrow> real" where
	"relu x = max 0 x"
 
end





theory AnglePIDANN_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>






\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>nodeOut211\<close>

nodeOut211 :: "real"
	
\<comment> \<open>layerRes21\<close>

layerRes21 :: "real"
	
\<comment> \<open>nodeOut112\<close>

nodeOut112 :: "real"
	
\<comment> \<open>nodeOut111\<close>

nodeOut111 :: "real"
	
\<comment> \<open>layerRes11\<close>

layerRes11 :: "real"
	
\<comment> \<open>layerRes02\<close>

layerRes02 :: "real"
	
\<comment> \<open>layerRes01\<close>

layerRes01 :: "real"
	
\<comment> \<open>terminate\<close>

terminate :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "ANNHiddenEvts = \<lbrace> 
	  layerRes11 \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
	"relu x = max 0 x"

locale AnglePIDANN
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
"Collator(i :: int, l :: int, n :: int, sum :: real) = (((((((((l = 1) \<and> (n = 1)) \<and> (i = 0)) & ((layerRes11!relu((sum + 0.125424)) \<rightarrow> Skip)))
  \<box>
  ((((l = 1) \<and> (n = 1)) \<and> (i = 1)) & ((nodeOut111?(x) \<rightarrow> Collator(l,n,(i - 1),(sum + x))))))
  \<box>
  ((((l = 1) \<and> (n = 1)) \<and> (i = 2)) & ((nodeOut112?(x) \<rightarrow> Collator(l,n,(i - 1),(sum + x))))))
  \<box>
  ((((l = 2) \<and> (n = 1)) \<and> (i = 0)) & ((layerRes21!relu((sum + -0.107753)) \<rightarrow> Skip))))
  \<box>
  ((((l = 2) \<and> (n = 1)) \<and> (i = 1)) & ((nodeOut211?(x) \<rightarrow> Collator(l,n,(i - 1),(sum + x)))))))" | 
"NodeIn(i :: int, l :: int, n :: int) = (((((((l = 1) \<and> (n = 1)) \<and> (i = 1)) & ((layerRes11?(x) \<rightarrow> (nodeOut111!(x * 1.22838) \<rightarrow> Skip))))
  \<box>
  ((((l = 1) \<and> (n = 1)) \<and> (i = 2)) & ((layerRes11?(x) \<rightarrow> (nodeOut112!(x * 0.132874) \<rightarrow> Skip)))))
  \<box>
  ((((l = 2) \<and> (n = 1)) \<and> (i = 1)) & ((layerRes21?(x) \<rightarrow> (nodeOut211!(x * 0.744636) \<rightarrow> Skip))))))" | 
"Node(inpSize :: int, l :: int, n :: int) = (((((l = 1) \<and> (n = 1)) & ((( \<interleave> i \<in> {1..inpSize} \<bullet>  NodeIn(l,n,i) )
  \<lbrakk> | \<lbrace> nodeOut112,nodeOut111 \<rbrace> | \<rbrakk> 
  (Collator(l,n,inpSize,0) \<Zhide> \<lbrace> nodeOut112,nodeOut111 \<rbrace>))))
  \<box>
  (((l = 2) \<and> (n = 1)) & ((( \<interleave> i \<in> {1..inpSize} \<bullet>  NodeIn(l,n,i) )
  \<lbrakk> | \<lbrace> nodeOut211 \<rbrace> | \<rbrakk> 
  (Collator(l,n,inpSize,0) \<Zhide> \<lbrace> nodeOut211 \<rbrace>))))))" | 
"HiddenLayer(s :: int, inpSize :: int, l :: int) = ((((l = 1) & (( \<lbrakk> \<lbrace> layerRes11 \<rbrace> \<rbrakk> i \<in> {1..s} \<bullet> Node(l,i,inpSize))))
  \<box>
  ((l = 2) & (( \<lbrakk> \<lbrace> layerRes21 \<rbrace> \<rbrakk> i \<in> {1..s} \<bullet> Node(l,i,inpSize))))))" | 
"HiddenLayers = HiddenLayer(1,1,2)" | 
"OutputLayer = ( \<lbrakk> \<lbrace> layerRes11 \<rbrace> \<rbrakk> i \<in> {1..1} \<bullet> Node(l,i,1))" | 
"ANN = (((HiddenLayers
  \<lbrakk> | \<lbrace> layerRes11 \<rbrace> | \<rbrakk> 
  OutputLayer) \<Zhide> ANNHiddenEvts);; ANN)" | 
"ANNRenamed = ((ANN [ layerRes01 \<mapsto> anewError,  
 layerRes02 \<mapsto> adiff,  
 layerRes21 \<mapsto> angleOutputE ]) \<triangle> (terminate \<rightarrow> Skip))"

\<comment> \<open>Main action of the process\<close>
definition "MainAction = cProcess ANNRenamed"

end
 
end





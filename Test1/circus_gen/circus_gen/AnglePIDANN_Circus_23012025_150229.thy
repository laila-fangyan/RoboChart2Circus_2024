theory AnglePIDANN_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>





\<comment> \<open>constant and function declaration/definition\<close>
definition weights :: "real list list list"
where "weights = [[[1.22838,0.132874]],[[0.744636]]]"
	
definition biases :: "real list list"
where "biases = [[0.125424],[(-0.107753)]]"
	
definition inRanges :: "(real \<times> real) list"
where "inRanges = [((-30.0),30.0),((-250.0),250.0)]"
	
definition outRanges :: "(real \<times> real) list"
where "outRanges = [((-1950.0),1950.0)]"
	
definition annRange :: "(real \<times> real)"
where "annRange = (0.0,1.0)"
	

\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>anewError\<close>

anewError :: "real"
	
\<comment> \<open>adiff\<close>

adiff :: "real"
	
\<comment> \<open>angleOutputE\<close>

angleOutputE :: "real"
	
\<comment> \<open>layerRes\<close>

layerRes :: "nat\<times>nat\<times>real"
	
\<comment> \<open>nodeOut\<close>

nodeOut :: "nat\<times>nat\<times>nat\<times>real"
	
\<comment> \<open>terminate\<close>

terminate :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>

definition relu :: "real \<Rightarrow> real" where
	"relu x = max 0 x"


locale AnglePIDANN
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"Collator(l :: int, n :: int, i :: int, sum :: real) = ((((l = 0) \<^bold>& ((layerRes\<^bold>!l\<^bold>!n\<^bold>!(relu(sum + (biases(l)(n)))) \<rightarrow> Skip)))
  \<box>
  ((l = 1) \<^bold>& ((nodeOut\<^bold>?x \<rightarrow> Collator(l,n,i-1,sum + x))))))" | 

"NodeIn(l :: int, n :: int, i :: int) = ((layerRes\<^bold>?x \<rightarrow> (nodeOut\<^bold>!l\<^bold>!n\<^bold>!i\<^bold>!(x * (weights(l)(n)(i))) \<rightarrow> Skip)))" | 

"Node(l :: int, n :: int, inpSize :: int) = ((( \<interleave> i \<in> {1..inpSize} \<bullet>  NodeIn(l,n,i) )
  \<lbrakk> | \<lbrace> nodeOut \<rbrace> | \<rbrakk> 
  (Collator(l,n,inpSize,0) \<Zhide> \<lbrace> nodeOut \<rbrace>)))" | 

"HiddenLayer(l :: int, s :: int, inpSize :: int) = (( \<lbrakk> \<lbrace> layerRes\<^bold>!2 \<rbrace> \<rbrakk> i \<in> {1..s} \<bullet> Node(l,i,inpSize)))" | 

"HiddenLayers = HiddenLayer(1,1,2)" | 

"OutputLayer = ( \<lbrakk> \<lbrace> layerRes\<^bold>!2 \<rbrace> \<rbrakk> i \<in> {1..1} \<bullet> Node(l,i,1))" | 

"ANN = ((HiddenLayers
  \<lbrakk> | \<lbrace> layerRes\<^bold>!2 \<rbrace> | \<rbrakk> 
  OutputLayer);; ANN)" | 

"Interpreter = ((;; );; Interpreter)" | 

"CircANN = (((Interpreter
  \<lbrakk> | \<lbrace> layerRes\<^bold>!2 \<rbrace> | \<rbrakk> 
  ANN) \<Zhide> \<lbrace> layerRes\<^bold>!2 \<rbrace>) \<triangle> (terminate \<rightarrow> Skip))"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess CircANN"

end
 




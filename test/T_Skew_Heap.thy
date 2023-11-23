theory T_Skew_Heap
  imports "../src/TimingFunction" "afp/Skew_Heap" "afp/Skew_Heap_Analysis"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
text \<open>merge contains let\<close>
text \<open>Failed to proove termination of meld:\<close>
define_time_fun Skew_Heap.insert
define_time_fun del_min

text \<open>Proove equality\<close>


end
theory T_Skew_Heap
  imports "../src/TimingFunction" "afp/Skew_Heap" "afp/Skew_Heap_Analysis"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
text \<open>Failed to proove termination of meld:\<close>
define_time_fun merge

text \<open>Proove equality\<close>
theorem meld: "T'_merge t1 t2 = T_merge t1 t2"
  apply (induction rule: T_merge.induct)
  using T'_merge.elims by auto

end
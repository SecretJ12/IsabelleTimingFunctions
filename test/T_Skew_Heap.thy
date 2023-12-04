theory T_Skew_Heap
  imports "../src/TimingFunction" "Skew_Heap.Skew_Heap" "Amortized_Complexity.Skew_Heap_Analysis"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
text \<open>Failed to proove termination of merge:\<close>
define_time_fun merge
(* Probably meld will be added *)

text \<open>Proove equality\<close>
theorem merge: "T'_merge t1 t2 = T_merge t1 t2"
  apply (induction rule: T_merge.induct)
  using T'_merge.elims by auto

end
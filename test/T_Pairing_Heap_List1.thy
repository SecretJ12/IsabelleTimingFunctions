theory T_Pairing_Heap_List1
  imports "../src/TimingFunction" "Pairing_Heap.Pairing_Heap_List1" "Amortized_Complexity.Pairing_Heap_List1_Analysis"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
define_time_fun merge
define_time_fun insert
define_time_fun pass\<^sub>1
define_time_fun pass\<^sub>2
define_time_fun del_min

text \<open>Proove equality\<close>
theorem merge: "T'_merge a b = 0"
  using T'_merge.elims by auto
theorem "T'_insert a b = 0"
  by (auto simp: merge)
theorem "T'_pass\<^sub>1 a = T\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 a"
  by (induction rule: T'_pass\<^sub>1.induct) (auto simp: merge)
theorem "T'_pass\<^sub>2 a = T\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 a"
  by (induction rule: T'_pass\<^sub>2.induct) (auto simp: merge)

end
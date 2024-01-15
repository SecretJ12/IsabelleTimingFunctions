theory T_Leftist_Heap
  imports "../src/Define_Time_Function" "HOL-Data_Structures.Leftist_Heap"
begin

declare [[time_prefix = "T'_"]]

text \<open>Helper functions\<close>
define_time_fun mht
define_time_fun node

text \<open>Define timing function\<close>
define_time_fun merge
define_time_fun insert
define_time_fun del_min

text \<open>Proove equality\<close>
lemma mht: "T'_mht r = 0"
  using T'_mht.elims by auto
lemma node: "T'_node l a r = 0"
  by (auto simp: mht)

theorem merge: "T'_merge x y = T_merge x y"
  by (induction rule: T_merge.induct) (auto simp: node mht)
theorem "T'_insert x y = T_insert x y"
  by (auto simp: merge T_insert_def)
theorem "T'_del_min t  = T_del_min t"
  by (cases t) (auto simp: merge)

end
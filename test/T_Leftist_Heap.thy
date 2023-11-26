theory T_Leftist_Heap
  imports "../src/TimingFunction" "HOL-Data_Structures.Leftist_Heap"
begin

declare [[time_prefix = "T'_"]]


text \<open>Define timing function\<close>
define_time_0 node
define_time_fun merge
define_time_fun insert
define_time_fun del_min

text \<open>Proove equality\<close>
theorem merge: "T'_merge x y = T_merge x y"
  by (induction rule: T_merge.induct) auto
theorem "T'_insert x y = T_insert x y + 1"
  by (auto simp: merge T_insert_def)
theorem "T'_del_min t  = T_del_min t + 1"
  by (cases t) (auto simp: merge)

end
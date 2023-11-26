theory T_Binomial_Heap
  imports "../src/TimingFunction" "HOL-Data_Structures.Binomial_Heap"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
define_time_fun link
define_time_0 rank
define_time_fun ins_tree
define_time_fun insert

text \<open>Only true with link being assumed constant\<close>
define_time_0 link
define_time_fun merge

define_time_0 root
define_time_0 min
define_time_fun get_min
define_time_fun get_min_rest
define_time_0 append
define_time_fun rev
define_time_fun del_min
                 

text \<open>Proove equality\<close>
theorem link: "T'_link t1 t2 = T_link t1 t2"
  using T'_link.elims by auto

theorem ins_tree: "T'_ins_tree t1 t2 = T_ins_tree t1 t2"
  sorry

theorem "T'_insert a t = T_insert a t"
  by (auto simp: ins_tree T_insert_def)

theorem merge: "T'_merge t1 t2 = T_merge t1 t2"
  by (induction rule: T_merge.induct) (auto simp: ins_tree)

theorem "t \<noteq> [] \<Longrightarrow> T'_get_min t = T_get_min t"
  by (induction rule: T_get_min.induct) auto

theorem get_min_rest: "t \<noteq> [] \<Longrightarrow> T'_get_min_rest t = T_get_min_rest t"
  by (induction rule: T_get_min_rest.induct) auto

theorem rev: "T'_rev xs = T_rev xs"
  by (induction xs) (auto simp: T_rev_def)

theorem "t \<noteq> [] \<Longrightarrow> T'_del_min t = T_del_min t"
  by (auto simp: get_min_rest rev T_del_min_def merge split: prod.split tree.split)

end
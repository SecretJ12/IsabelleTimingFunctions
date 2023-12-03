theory T_Splay_Tree
  imports "../src/TimingFunction" "Splay_Tree.Splay_Tree" "Amortized_Complexity.Splay_Tree_Analysis_Base"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
define_time_0 cmp
define_time_fun splay with splay.simps(1) splay_code
text \<open>splay contains functions with conditions\<close>
define_time_fun splay_max
define_time_fun insert
define_time_fun delete

value "T'_splay (1::nat) \<langle>Leaf, 1, Leaf\<rangle>"

text \<open>Proove equality\<close>
theorem splay: "T'_splay x t = T_splay x t"
  by (induction x t rule: T_splay.induct)  (auto split: tree.split)

theorem splay_max: "T'_splay_max t = T_splay_max t"
  by (induction rule: T_splay_max.induct) auto

theorem "T'_insert x t = T_insert x t"
  by (auto simp: T_insert_def splay)

theorem "T'_delete x t = T_delete x t"
  by (auto simp: T_delete_def splay splay_max split: tree.split)

end
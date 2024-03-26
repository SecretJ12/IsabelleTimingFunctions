theory T_Splay_Tree
  imports "../src/Define_Time_Function" "Splay_Tree.Splay_Tree" "Amortized_Complexity.Splay_Tree_Analysis_Base"
begin

declare [[time_prefix = "T'_"]]

text \<open>Helper functions\<close>
time_fun cmp

text \<open>Define timing function\<close>
text \<open>splay contains functions with conditions, instead use the proven code:\<close>
time_fun splay equations splay.simps(1) splay_code
time_fun splay_max
time_definition insert
time_definition delete

text \<open>Proove equality\<close>
theorem splay: "T'_splay x t = T_splay x t"
  apply (induction x t rule: T_splay.induct)
   apply simp
  subgoal for x AB b CD
    by (cases "cmp x b") (auto split: tree.splits)
  done

theorem splay_max: "T'_splay_max t = T_splay_max t"
  by (induction rule: T_splay_max.induct) (auto split: tree.split)

theorem "T'_insert x t = T_insert x t"
  by (auto simp: T_insert_def splay split: tree.split)

theorem "T'_delete x t = T_delete x t"
  by (auto simp: T_delete_def splay splay_max split: tree.split)

end
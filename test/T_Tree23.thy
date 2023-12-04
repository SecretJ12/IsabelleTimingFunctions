theory T_Tree23
  imports "../src/TimingFunction" "HOL-Data_Structures.Tree23_of_List"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
define_time_fun join_adj
define_time_fun join_all
define_time_fun tree23_of_list

text \<open>Proove equality\<close>
theorem join_adj: "\<forall>a. t \<noteq> T a \<Longrightarrow> T'_join_adj t = T_join_adj t"
  by (induction t rule: join_adj.induct) auto

theorem join_all: "T'_join_all t = T_join_all t"
  by (induction rule: T_join_all.induct) (auto simp: join_adj)

lemma leaves: "T'_leaves xs = T_leaves xs"
  by (induction xs) auto

theorem "T'_tree23_of_list xs = T_tree23_of_list xs - 1"
  by (induction xs) (auto simp: leaves T_tree23_of_list_def join_all)

end
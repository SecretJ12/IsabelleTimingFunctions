theory T_BinomialHeap
  imports "../src/TimingFunction" "HOL-Data_Structures.Binomial_Heap"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
text \<open>link contains let via =:\<close>
text \<open>ins_tree contains\<close>
text \<open>insert contains\<close>
text \<open>merge contains\<close>
define_time_0 root
define_time_0 min
define_time_fun get_min
text \<open>get_min_rest contains\<close>
define_time_0 append
define_time_fun rev
text \<open>del_min contains\<close>
                 

text \<open>Proove equality\<close>
theorem "t \<noteq> [] \<Longrightarrow> T'_get_min t = T_get_min t"
  by (induction rule: T_get_min.induct) auto

theorem "T'_rev xs = T_rev xs"
  by (induction xs) (auto simp: T_rev_def)

end
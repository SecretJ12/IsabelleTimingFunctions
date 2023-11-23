theory T_Splay_Tree
  imports "../src/TimingFunction" "afp/Splay_Tree" "afp/Splay_Tree_Analysis_Base"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
text \<open>splay contains functions with conditions\<close>
define_time_fun splay_max
text \<open>insert uses splay\<close>
text \<open>delete uses splay\<close>


text \<open>Proove equality\<close>

theorem "T'_splay_max t = T_splay_max t"
  by (induction rule: T_splay_max.induct) auto

end
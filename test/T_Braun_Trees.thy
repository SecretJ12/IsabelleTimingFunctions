theory T_Braun_Trees
  imports "../src/TimingFunction" "afp/Priority_Queue_Braun"
begin

declare [[time_prefix = "T'_"]]


text \<open>Define timing function\<close>
define_time_fun insert
define_time_fun sift_down
define_time_fun del_left
define_time_fun del_min

text \<open>Proove equality\<close>
theorem "T'_insert a t = T_insert a t"
  by (induction t arbitrary: a) auto

theorem sift_down: "T'_sift_down l a r = T_sift_down l a r"
  sorry
theorem del_left: "t \<noteq> \<langle>\<rangle> \<Longrightarrow> T'_del_left t = T_del_left t"
  by (induction rule: T_del_left.induct) auto

theorem "T'_del_min t = T_del_min t"
  by (induction rule: T_del_min.induct) (auto simp: sift_down del_left split: prod.split)

end
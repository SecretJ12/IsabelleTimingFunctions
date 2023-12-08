theory T_Braun_Trees
  imports "../src/TimingFunction" "Priority_Queue_Braun.Priority_Queue_Braun"
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

theorem sift_down: "braun(Node l a r) \<Longrightarrow> T'_sift_down l a r = T_sift_down l a r"
  by (induction l a r rule: T_sift_down.induct) auto
theorem del_left: "t \<noteq> \<langle>\<rangle> \<Longrightarrow> T'_del_left t = T_del_left t"
  by (induction rule: T_del_left.induct) auto

lemma br:
  assumes "braun (Node l x r)"
    and   "(y,l') = del_left l"
    and   "l \<noteq> Leaf"
   shows  "braun (Node r y l')"
proof -
  have 1: "braun l" "braun r" using assms(1) by auto
  then have 2: "braun l'" using assms del_left_braun by metis
  from assms del_left_size[of l y l']
  have 3: "size l' + 1 = size r \<or> size l' = size r" by simp
  with assms 3 2 show ?thesis by auto
qed

theorem "braun t \<Longrightarrow> T'_del_min t = T_del_min t"
proof (induction rule: T_del_min.induct)
  case (3 v va vb x r)
  with br[of r "fst (del_left \<langle>v, va, vb\<rangle>)"  "snd (del_left \<langle>v, va, vb\<rangle>)"]
  have "braun \<langle>r, fst (del_left \<langle>v, va, vb\<rangle>), snd (del_left \<langle>v, va, vb\<rangle>)\<rangle>"
    by (metis br prod.exhaust_sel tree.discI)
  with 3 show ?case
    by (simp add: split_beta del_left sift_down)
qed simp+

end

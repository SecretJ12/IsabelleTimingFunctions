theory T_Queue_2Lists
  imports "../src/TimingFunction" "HOL-Data_Structures.Queue_2Lists"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
define_time_fun norm
define_time_fun enq
define_time_0 tl
define_time_fun deq
define_time_fun first
define_time_fun is_empty


text \<open>Proove equality\<close>
lemma itrev: "T'_itrev xs ys = T_itrev xs ys"
  by (induction xs arbitrary: ys) auto

theorem norm: "T'_norm q = T_norm q"
  by (cases q) (auto simp: itrev)

theorem "T'_enq a q = T_enq a q"
  by (cases q) (auto simp: norm)

theorem "T'_deq q = T_deq q"
  by (cases q) (auto simp: norm)

theorem "0 < length fs \<Longrightarrow> T'_first (fs,rs) = T_first (fs,rs)"
  by (cases fs) auto

theorem "T'_is_empty q = T_is_empty q"
  by (cases q) auto

end
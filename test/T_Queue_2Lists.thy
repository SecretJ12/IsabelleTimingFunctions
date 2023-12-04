theory T_Queue_2Lists
  imports "../src/TimingFunction" "HOL-Data_Structures.Queue_2Lists"
begin

declare [[time_prefix = "T'_"]]

text \<open>Define timing function\<close>
define_time_fun norm
define_time_fun enq
define_time_fun deq
define_time_fun first
define_time_fun is_empty


text \<open>Proove equality\<close>
lemma itrev: "T'_itrev xs ys = T_itrev xs ys"
  by (induction xs arbitrary: ys) auto

theorem norm: "T'_norm q = T_norm q - 1" (* TODO *)
  by (cases q) (auto simp: itrev)

theorem "T'_enq a q = T_enq a q - 2" (* TODO *)
  apply (cases q)
  using T'_tl.elims by (auto simp: norm)

theorem "T'_deq q = T_deq q - 2" (* TODO *)
  apply (cases q)
  using T'_tl.elims by (auto simp: norm)

theorem "0 < length fs \<Longrightarrow> T'_first (fs,rs) = T_first (fs,rs) - 1" (* TODO *)
  by (cases fs) auto

theorem "T'_is_empty q = T_is_empty q - 1" (* TODO *)
  by (cases q) auto

end
theory T_Selection
  imports "../src/TimingFunction" "HOL-Data_Structures.Selection"
begin

declare [[time_prefix = "T'_"]]

text \<open>Assume size is used on lists\<close>
fun size :: "'a list \<Rightarrow> nat" where
  "size [] = 0"
| "size (_#xs) = size xs + 1"
define_time_fun size

text \<open>Transformation of the functions\<close>
define_time_fun chop
text \<open>partition3 is partial as filter is partial\<close>
define_time_fun slow_select
text \<open>slow_median needs T_List as length cannot be converted correctly otherwise\<close>
define_time_fun slow_median

text \<open>Proofs about equality\<close>
theorem "T'_chop n xs = T_chop n xs"
  oops

lemma insert1: "T'_insort1 x xs = T_insort1 x xs"
  by (induction xs) auto
theorem insert: "T'_insort xs = T_insort xs"
  by (induction xs) (auto simp: insert1)
lemma nth: "n < length xs \<Longrightarrow> T'_nth xs n = T_nth xs n"
proof (induction n arbitrary: xs)
  case (0 xs) thus ?case by (cases xs) (auto simp: T_nth.simps)
next
  case (Suc n xs) thus ?case by (cases xs) (auto simp: T_nth.simps)
qed
theorem slow_select: "n < length xs \<Longrightarrow> T'_slow_select n xs = T_slow_select n xs"
  by (auto simp: insert nth T_slow_select_def length_insort)

theorem "T'_slow_median xs = T_slow_median xs"
  oops

end
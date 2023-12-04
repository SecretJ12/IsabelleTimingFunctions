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
define_time_0 length (* is wrong, got corrected *)
define_time_fun slow_median

declare [[time_prefix = "T''_"]]
text \<open>mom_select uses a lambda through map\<close>

text \<open>Proofs about equality\<close>
theorem "T'_chop n xs = T_chop n xs"
  oops

lemma insort1: "T'_insort1 x xs = T_insort1 x xs"
  by (induction xs) auto
theorem insort: "T'_insort xs = T_insort xs"
  by (induction xs) (auto simp: insort1)
lemma nth: "n < length xs \<Longrightarrow> T'_nth xs n = T_nth xs n"
proof (induction n arbitrary: xs)
  case (0 xs) thus ?case by (cases xs) (auto simp: T_nth.simps)
next
  case (Suc n xs) thus ?case by (cases xs) (auto simp: T_nth.simps)
qed
theorem slow_select: "n < length xs \<Longrightarrow> T'_slow_select n xs = T_slow_select n xs - 1" (* TODO *)
  by (auto simp: insort nth T_slow_select_def length_insort)

lemma slow_median_n: "xs \<noteq> [] \<Longrightarrow> (length xs - 1) div 2 < length xs"
  by (induction xs) auto
theorem "xs \<noteq> [] \<Longrightarrow> T'_slow_median xs = T_slow_median xs - 2" (* TODO *)
  using slow_median_n slow_select by (auto simp: T_slow_median_def)

end
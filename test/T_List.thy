theory T_List
  imports "../src/TimingFunction" "HOL-Data_Structures.Time_Funs"
begin

fun length :: "'a list \<Rightarrow> nat" where
  "length [] = 0"
| "length (_#xs) = length xs + 1"

declare [[time_prefix = "T'_"]]
define_time_fun length
text \<open>map is partial\<close> (* TODO *)
text \<open>filter is partial\<close> (* TODO *)
define_time_fun take
define_time_fun drop

fun td_schema :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "td_schema _ [] = []"
| "td_schema 0 xs = xs"
| "td_schema (Suc n) (x#xs) = td_schema n xs"

lemma "T'_length xs = T_length xs"
  by (induction xs) (auto simp: T_length.simps)
lemma "T'_take n xs = T_take n xs"
  by (induction n xs rule: td_schema.induct) auto
lemma "T'_drop n xs = T_drop n xs"
  by (induction n xs rule: td_schema.induct) auto

end
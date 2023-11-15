theory T_List
  imports "../src/TimingFunction"
begin

fun length :: "'a list \<Rightarrow> nat" where
  "length [] = 0"
| "length (_#xs) = length xs + 1"

define_atime_fun length
define_atime_fun take
define_atime_fun drop

fun t_length :: "'a list \<Rightarrow> nat" where
  "t_length [] = 1"
| "t_length (_#xs) = t_length xs + 1"

fun t_take :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_take _ [] = 1"
| "t_take n (_#xs) = (case n of 0 \<Rightarrow> 1 | Suc n' \<Rightarrow> t_take n' xs + 1)"

fun t_drop :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_drop _ [] = 1"
| "t_drop n (_#xs) = (case n of 0 \<Rightarrow> 1 | Suc n' \<Rightarrow> t_drop n' xs + 1)"

fun td_schema :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "td_schema _ [] = []"
| "td_schema 0 xs = xs"
| "td_schema (Suc n) (x#xs) = td_schema n xs"

lemma "t_length xs = T_length xs"
  by (induction xs) auto
lemma "t_take n xs = T_take n xs"
  by (induction n xs rule: td_schema.induct) auto
lemma "t_drop n xs = T_drop n xs"
  by (induction n xs rule: td_schema.induct) auto

end
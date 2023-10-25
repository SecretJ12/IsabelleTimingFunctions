theory Test
  imports "TimingFunction"
begin

chapter \<open>Definition on example\<close>

text \<open>The following function sums up all integers from 0 to n\<close>
fun f :: "nat \<Rightarrow> nat" where
  "f 0 = 0"
| "f (Suc n) = Suc n + f n"

text \<open>It should be translated into the following timing function\<close>
fun T_f :: "nat \<Rightarrow> nat" where
  "T_f 0 = 1"
| "T_f (Suc n) = T_f n + 1"


text \<open>Hereby we run through the following steps:
\<E>\<lbrakk>f 0 = 0\<rbrakk>
= (T_f 0 = \<T>\<lbrakk>0] + 1)
= (T_f 0 = 1 + 1)
\<leadsto> (T_f 0 = 1)
and
\<E>\<lbrakk>f (Suc n) = Suc n + f n\<rbrakk>
= (T_f (Suc n) = \<T>\<lbrakk>Suc n + f n\<rbrakk> + 1)
= (T_f (Suc n) = 1 + \<T>\<lbrakk>Suc n\<rbrakk> + \<T>\<lbrakk>f n\<rbrakk> + 1)
= (T_f (Suc n) = 1 + 1 + \<T>\<lbrakk>f n\<rbrakk> + 1)
= (T_f (Suc n) = 1 + 1 + T_f n + \<T>\<lbrakk>1\<rbrakk> + 1)
= (T_f (Suc n) = 1 + 1 + T_f n + 1 + 1)
= (T_f (Suc n) = T_f n + 4)
\<leadsto> (T_f (Suc n) = T_f n + 1)\<close>

fun g :: "nat \<Rightarrow> nat" where
  "g 0 = 1"
| "g (Suc n) = Suc n + g n"

text \<open>The same function should be generated with the following command\<close> (* TODO *)
define_time_fun g

subsection \<open>Function T_g should now be defined\<close>
value "T_g 1"

subsection \<open>Example proof (Conversion still TODO)\<close>
lemma "T_f n = Suc n"
  by (induction n) simp+

(* Simple working example *)
fun h :: "'a list \<Rightarrow> nat" where
  "h [] = 7"
| "h (_#xs) = h xs"
define_time_fun h

end
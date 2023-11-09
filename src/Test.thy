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
| "g (Suc n) = g n"
function (domintros) t_g :: "nat \<Rightarrow> nat" where
  "t_g 0 = 1"
| "t_g (Suc n) = 1 + t_g n"
  by pat_completeness auto

text \<open>The same function should be generated with the following command\<close>
define_time_fun g

subsection \<open>Function T_g should now be defined\<close>
value "T_g 1"

subsection \<open>Example proof (Conversion still TODO)\<close>
lemma "T_f n = Suc n"
  by (induction n) simp+

(* Simple working example *)
fun h :: "'a list \<Rightarrow> nat" where
  "h [] = 1"
| "h (_#xs) = h xs"
define_time_fun h

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys"
| "itrev (x#xs) ys = itrev xs (x#ys)"
define_time_fun itrev

fun is_odd :: "nat \<Rightarrow> bool" where
  "is_odd 0 = False"
| "is_odd (Suc n) = (if is_odd n then \<not> (is_odd n) else \<not> (is_odd n))"
define_atime_fun is_odd

value "(T_is_odd 0, T_is_odd 1, T_is_odd 2, T_is_odd 3)"
lemma "T_is_odd n = 2^(Suc n) - 1"
proof (induction n)
  case (Suc n)
  have "4 \<le> (2::nat)^(Suc (Suc n))"
    apply (induction n)
    by auto
  have "T_is_odd (Suc n) = 1 + (2^(Suc (Suc n)) - 2)"
    using Suc.IH
    by simp
  also have "\<dots> = 2^(Suc (Suc n)) - 1"
    using \<open>4 \<le> 2 ^ Suc (Suc n)\<close> by linarith
  
  finally show ?case.
qed simp

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 y = y"
| "add (Suc x) y = add x (Suc y)"
fun mul where
  "mul 0 y = 0"
| "mul (Suc 0) y = y"
| "mul (Suc (Suc x)) y = add y (mul (Suc x) y)"
define_atime_fun mul

lemma [simp]: "T_add n m = Suc n"
  by (induction n arbitrary: m) auto
lemma "T_mul (Suc n) m = 1 + n * (Suc (Suc m))"
  by (induction n arbitrary: m) auto

function p :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "p a b = (if a < b then p (Suc a) b else a)"
  by auto
termination
  by (relation "measure (\<lambda>(a,b). b - a)") auto
define_atime_fun p

function q :: "nat \<Rightarrow> nat" where
  "q a = (if a < (Suc (Suc (Suc (Suc 0)))) then q (Suc a) else a)"
  by auto
termination
  by (relation "measure (\<lambda>a. 4 - a)") auto
define_atime_fun q

end
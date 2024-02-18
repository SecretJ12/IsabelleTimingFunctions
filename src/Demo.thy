theory Demo
  imports Define_Time_Function "Splay_Tree.Splay_Tree"
begin

text \<open>Simple example\<close>
fun sum :: "nat \<Rightarrow> nat" where
  "sum 0 = 0"
| "sum (Suc n) = Suc n + sum n"
define_time_fun sum

lemma "sum n = (Suc n)*n div 2"
  by (induction n) auto



text \<open>Non-recursive functions with reduced if-else\<close>
fun test :: "nat \<Rightarrow> nat list" where
  "test n = (if n = 7 then [1,2] else [])"
define_time_fun test




text \<open>Termination proof over dom\<close>
function collatz :: "nat \<Rightarrow> nat" where
  "collatz n = (if n \<le> 1 then 0 else if even n then 1 + collatz (n div 2) else 1 + collatz (3 * n + 1))"
  by auto
termination sorry

define_time_0 "(dvd)"
define_time_fun collatz



text \<open>Manual termination proof\<close>
function sum_to :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_to i j = (if j \<le> i then 0 else i + sum_to (Suc i) j)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(i,j). j - i)") auto

define_time_function sum_to
termination
  by (relation "measure (\<lambda>(i,j). j - i)") auto




text \<open>Mutual recursion\<close>
fun even :: "nat \<Rightarrow> bool"
  and odd :: "nat \<Rightarrow> bool" where
  "even 0 = True"
| "odd 0 = False"
| "even (Suc n) = odd n"
| "odd (Suc n) = even n"
define_time_fun even odd




text \<open>Explicitely specify equations\<close>
define_time_fun cmp
define_time_fun splay equations splay.simps(1) splay_code

end
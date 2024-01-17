theory Test
  imports "Define_Time_Function"
begin

chapter \<open>Definition on example\<close>

text \<open>The following function sums up all integers from 0 to n\<close>
fun sum :: "nat \<Rightarrow> nat" where
  "sum 0 = 0"
| "sum (Suc n) = Suc n + sum n"

text \<open>It should be translated into the following timing function\<close>
fun t_sum :: "nat \<Rightarrow> nat" where
  "t_sum 0 = 1"
| "t_sum (Suc n) = t_sum n + 1"

text \<open>The same function should be generated with the following command\<close>
define_time_fun sum

text \<open>Proof\<close>
lemma "t_sum n = T_sum n"
  by (induction n) auto

text \<open>The command should work for all input types\<close>
fun len :: "'a list \<Rightarrow> nat" where
  "len [] = 0"
| "len (_#xs) = Suc (len xs)"
define_time_fun len

lemma "T_len xs = Suc (length (xs))"
  by (induction xs) auto

text \<open>An also multiple inputs and different output types\<close>
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys"
| "itrev (x#xs) ys = itrev xs (x#ys)"
define_time_fun itrev

lemma "T_itrev xs ys = 1 + length xs"
  by (induction xs arbitrary: ys) auto

text \<open>Used functions of the same theory should be converted automatically\<close>
fun itrev' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev' [] ys = ys"
| "itrev' (x#xs) ys = itrev' xs (x#ys)"
fun Itrev' :: "'a list \<Rightarrow> 'a list" where
  "Itrev' xs = itrev' xs []"
define_time_fun itrev'
define_time_fun Itrev'
value "T_Itrev' [a, b, c]"
lemma T_itrev': "T_itrev' xs ys = 1 + length xs"
  by (induction xs arbitrary: ys) auto
lemma "T_Itrev' xs = 1 + length xs"
  by (simp add: T_itrev')

text \<open>If conditions should be handled accordingly\<close>
fun is_odd :: "nat \<Rightarrow> bool" where
  "is_odd 0 = False"
| "is_odd (Suc n) = (if is_odd n then \<not> (is_odd n) else \<not> (is_odd n))"
fun t_is_odd :: "nat \<Rightarrow> nat" where
  "t_is_odd 0 = 1"
| "t_is_odd (Suc n) = 1 + (if is_odd n then t_is_odd n else t_is_odd n) + t_is_odd n"
define_time_fun is_odd
lemma "T_is_odd n = t_is_odd n"
  by (induction n) auto

text \<open>Example proof\<close>
lemma "T_is_odd n = 2^(Suc n) - 1"
proof (induction n)
  case (Suc n)
  have "T_is_odd (Suc n) = 1 + T_is_odd n + T_is_odd n"
    by simp
  also have "\<dots> = 2^(Suc (Suc n)) - 1"
    using Suc.IH by simp
  finally show ?case.
qed simp

fun gt_9 :: "nat \<Rightarrow> bool" where
  "gt_9 n = (n > 9)"
fun T_gt_9 :: "nat \<Rightarrow> nat" where
  "T_gt_9 _ = 9"
fun empty_if :: "nat \<Rightarrow> bool" where
  "empty_if n = (if gt_9 n then True else False)"
fun t_empty_if :: "nat \<Rightarrow> nat" where
  "t_empty_if n = 9"
define_time_fun empty_if
lemma "T_empty_if n = t_empty_if n "
  by simp

text \<open>More complex example for non asymptotic version\<close>
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 y = y"
| "add (Suc x) y = add x (Suc y)"
fun mul where
  "mul 0 y = 0"
| "mul (Suc 0) y = y"
| "mul (Suc (Suc x)) y = add y (mul (Suc x) y)"
define_time_fun add
define_time_fun mul

text \<open>Example proof\<close>
lemma T_add: "T_add n m = 1 + n"
  by (induction n arbitrary: m) auto
lemma "T_mul (Suc n) m = 1 + n*(m+2)"
  by (induction n arbitrary: m) (auto simp: T_add)

text \<open>The command should define the timing function and prove termination with help of the original function\<close>
function terminationA :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "terminationA a b = (if a < b then terminationA (Suc a) b else a)"
  by auto
termination
  by (relation "measure (\<lambda>(a,b). b - a)") auto
define_time_fun terminationA
lemma "T_terminationA 10 22 = 13"
  by simp

function terminationB :: \<open>nat \<Rightarrow> bool\<close> where
\<open>terminationB n = (if n \<le> 1 then True else if (Suc 1) dvd n then terminationB (n div (Suc 1)) else terminationB ((Suc (Suc 1)) * n + 1))\<close>
  by auto
termination sorry
define_time_0 "(dvd)"
define_time_fun terminationB

text \<open>The command should handle case expressions\<close>
fun default :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" where
  "default opt d = (case opt of None \<Rightarrow> d | Some v \<Rightarrow> v)"
fun t_default :: "'a option \<Rightarrow> 'a \<Rightarrow> nat" where
  "t_default opt d = 0"
define_time_fun default
lemma "T_default opt d = t_default opt d"
  by auto

fun caseAdd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "caseAdd a b = (case a of 0 \<Rightarrow> b | Suc a' \<Rightarrow> Suc (caseAdd a' b))"
fun t_caseAdd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "t_caseAdd a b = 1 + (case a of 0 \<Rightarrow> 0 | Suc a' \<Rightarrow> t_caseAdd a' b)"
define_time_fun caseAdd
lemma "T_caseAdd a b = t_caseAdd a b"
  by (induction a) auto

fun caseAdd' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "caseAdd' a b = (case a of 0 \<Rightarrow> b | Suc a' \<Rightarrow> Suc (caseAdd' a' b))"
fun t_caseAdd' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "t_caseAdd' a b = 1 + (case a of 0 \<Rightarrow> 0 | Suc a' \<Rightarrow> t_caseAdd' a' b)"
define_time_fun caseAdd'
lemma "T_caseAdd' a b = t_caseAdd' a b"
  by (induction a) auto

text \<open>Edge case of reduced cases\<close>
fun edge_case :: "nat * nat \<Rightarrow> nat" where
  "edge_case n = (case n of (a, b) \<Rightarrow> add a b)"
define_time_fun edge_case

text \<open>Allow conversion of library functions\<close>
define_time_fun append
define_time_fun rev
lemma T_append_length: "T_append xs ys = Suc (length xs)"
  by (induction xs) auto
lemma "T_rev xs = \<Sum>{1..Suc (length xs)}"
  by (induction xs) (auto simp: T_append_length)

text \<open>Also allow definitions to be converted\<close>
definition wrapper where "wrapper a b = add a b"
define_time_fun wrapper


text \<open>Handle let expressions correctly\<close>
datatype dummyTree = Leaf | Node dummyTree dummyTree
fun dummy where "dummy T = T"
fun mirror :: "dummyTree \<Rightarrow> dummyTree" where
  "mirror Leaf = Leaf"
| "mirror (Node l r) =
    (let l' = mirror l in let r' = mirror r
    in dummy (Node r' l'))"
define_time_fun dummy
define_time_fun mirror
fun t_mirror :: "dummyTree \<Rightarrow> nat" where
  "t_mirror Leaf = 1"
| "t_mirror (Node l r) = 1 + T_mirror l + T_mirror r +
    (let l' = mirror l in let r' = mirror r
     in T_dummy (Node r' l'))"
lemma "T_mirror t = t_mirror t"
  by (induction t) auto

text \<open>Handle pattern matching in let\<close>
fun first :: "'a * 'b \<Rightarrow> 'a" where
  "first pair =
    (let (a,b) = dummy pair in dummy a)"
define_time_fun first
fun t_first :: "'a * 'b \<Rightarrow> nat" where
  "t_first pair =
    T_dummy pair + (let (a,b) = dummy pair in T_dummy a)"
lemma "T_first pair = t_first pair"
  by auto

fun comp :: "nat \<Rightarrow> nat" where
  "comp n = (n*5 div 7+1)*0"
lemma comp_simp: "comp n = 0" by simp

text \<open>Should take thm terms as argument for function terms\<close>
define_time_fun comp equations comp_simp

text \<open>Non recursive function should be without cost for calling the function\<close>
fun divide :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "divide a b = a div b"
define_time_fun divide
lemma "T_divide a b = 0"
  by simp

ML \<open>
HOLogic.mk_fst (Free ("a",@{typ "nat*nat"}))
\<close>

text \<open>Should be able to translate functions with function as argument\<close>
fun t_map :: "(('a \<Rightarrow> 'b) * ('a \<Rightarrow> nat)) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_map f [] = 1"
| "t_map f (x#xs) = 1 + snd f x + t_map f xs"
define_time_fun map
fun leng :: "'a list \<Rightarrow> nat" where
  "leng [] = 0" | "leng (x#xs) = Suc (leng xs)"
define_time_fun leng
lemma leng: "T_leng xs = Suc (length xs)"
  by (induction xs) auto
lemma "T_map (leng,T_leng) xs = Suc (length xs) + length xs + foldr ((+) o length) xs 0"
  by (induction xs) (auto simp: leng)
lemma "T_map (leng,T_leng) xs = t_map (leng,T_leng) xs"
  by (induction xs) auto

text \<open>Functions with function should be called correctly\<close>
fun is_zero :: "nat \<Rightarrow> bool" where "is_zero 0 = True" | "is_zero _ = False"
fun find_zero :: "nat list \<Rightarrow> nat list" where
  "find_zero xs = filter is_zero xs"
define_time_fun is_zero
define_time_fun filter
define_time_fun find_zero
fun t_is_zero :: "nat \<Rightarrow> nat" where
  "t_is_zero n = 0"
fun t_filter :: "(('a \<Rightarrow> bool) * ('a \<Rightarrow> nat)) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_filter _ [] = 1"
| "t_filter (p,t_p) (x#xs) = 1 + t_filter (p,t_p) xs + t_p x"
lemma filter: "t_filter (p,t_p) xs = T_filter (p,t_p) xs"
  by (induction xs) auto
fun t_find_zero :: "nat list \<Rightarrow> nat" where
  "t_find_zero xs = t_filter (is_zero,t_is_zero) xs"
lemma "t_find_zero xs = T_find_zero xs"
  apply (induction xs)
  using T_is_zero.elims by (auto simp: filter)

text \<open>More functions to test functions as arguments\<close>
fun revmap' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "revmap' f [] ys = ys"
| "revmap' f (x#xs) ys = revmap' f xs (f x # ys)"
fun revmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "revmap f xs = revmap' f xs []"
define_time_fun revmap'
define_time_fun revmap
lemma revmap': "T_revmap' (f,T_f) xs ys = Suc (length xs) + foldr ((+) o T_f) xs 0"
  by (induction xs arbitrary: ys) auto
lemma "T_revmap (f,T_f) xs = Suc (length xs) + foldr ((+) o T_f) xs 0"
  by (simp add: revmap')

fun func_in_pair :: "(nat * (nat \<Rightarrow> bool)) \<Rightarrow> bool" where
  "func_in_pair (0, f) = f 0"
| "func_in_pair (Suc n, f) = f n"
fun t_func_in_pair :: "(nat * ((nat \<Rightarrow> bool) * (nat \<Rightarrow> nat))) \<Rightarrow> nat" where
  "t_func_in_pair (0, f) = snd f 0"
| "t_func_in_pair (Suc n, f) = snd f n"
define_time_fun func_in_pair
lemma "T_func_in_pair (n,f) = t_func_in_pair (n,f)"
  by (induction n) auto

fun even :: "nat \<Rightarrow> bool" 
  and odd :: "nat \<Rightarrow> bool" where
  "even 0 = True"
| "odd 0 = False"
| "even (Suc n) = odd n"
| "odd (Suc n) = even n"

define_time_fun even odd

end
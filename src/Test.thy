theory Test
  imports Define_Time_Function
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
time_fun sum

text \<open>Proof\<close>
lemma "t_sum n = T_sum n"
  by (induction n) auto

text \<open>The command should work for all input types\<close>
fun len :: "'a list \<Rightarrow> nat" where
  "len [] = 0"
| "len (_#xs) = Suc (len xs)"
time_fun len

lemma "T_len xs = Suc (length (xs))"
  by (induction xs) auto

text \<open>An also multiple inputs and different output types\<close>
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys"
| "itrev (x#xs) ys = itrev xs (x#ys)"
time_fun itrev

lemma "T_itrev xs ys = 1 + length xs"
  by (induction xs arbitrary: ys) auto

text \<open>Used functions of the same theory should be converted automatically\<close>
fun itrev' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev' [] ys = ys"
| "itrev' (x#xs) ys = itrev' xs (x#ys)"
fun Itrev' :: "'a list \<Rightarrow> 'a list" where
  "Itrev' xs = itrev' xs []"
time_fun itrev'
time_fun Itrev'
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
time_fun is_odd
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
time_fun empty_if
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
time_fun add
time_fun mul

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
time_fun terminationA
lemma "T_terminationA 10 22 = 13"
  by simp

ML \<open>
@{term "T_terminationA_dom"}
\<close>

function terminationB :: \<open>nat \<Rightarrow> bool\<close> where
\<open>terminationB n = (if n \<le> 1 then True else if (Suc 1) dvd n then terminationB (n div (Suc 1)) else terminationB ((Suc (Suc 1)) * n + 1))\<close>
  by auto
termination sorry
time_fun_0 "(dvd)"
time_fun terminationB

text \<open>The command should handle case expressions\<close>
fun default :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" where
  "default opt d = (case opt of None \<Rightarrow> d | Some v \<Rightarrow> v)"
fun t_default :: "'a option \<Rightarrow> 'a \<Rightarrow> nat" where
  "t_default opt d = 0"
time_fun default
lemma "T_default opt d = t_default opt d"
  by auto

fun caseAdd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "caseAdd a b = (case a of 0 \<Rightarrow> b | Suc a' \<Rightarrow> Suc (caseAdd a' b))"
fun t_caseAdd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "t_caseAdd a b = 1 + (case a of 0 \<Rightarrow> 0 | Suc a' \<Rightarrow> t_caseAdd a' b)"
time_fun caseAdd
lemma "T_caseAdd a b = t_caseAdd a b"
  by (induction a) auto

fun caseAdd' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "caseAdd' a b = (case a of 0 \<Rightarrow> b | Suc a' \<Rightarrow> Suc (caseAdd' a' b))"
fun t_caseAdd' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "t_caseAdd' a b = 1 + (case a of 0 \<Rightarrow> 0 | Suc a' \<Rightarrow> t_caseAdd' a' b)"
time_fun caseAdd'
lemma "T_caseAdd' a b = t_caseAdd' a b"
  by (induction a) auto

text \<open>Edge case of reduced cases\<close>
fun edge_case :: "nat * nat \<Rightarrow> nat" where
  "edge_case n = (case n of (a, b) \<Rightarrow> add a b)"
time_fun edge_case

text \<open>Allow conversion of library functions\<close>
time_fun append
time_fun rev
lemma T_append_length: "T_append xs ys = Suc (length xs)"
  by (induction xs) auto
lemma "T_rev xs = \<Sum>{1..Suc (length xs)}"
  by (induction xs) (auto simp: T_append_length)

text \<open>Also allow definitions to be converted\<close>
definition wrapper where "wrapper a b = add a b"
time_fun wrapper


text \<open>Handle let expressions correctly\<close>
datatype dummyTree = Leaf | Node dummyTree dummyTree
fun dummy where "dummy T = T"
fun mirror :: "dummyTree \<Rightarrow> dummyTree" where
  "mirror Leaf = Leaf"
| "mirror (Node l r) =
    (let l' = mirror l in let r' = mirror r
    in dummy (Node r' l'))"
time_fun dummy
time_fun mirror
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
time_fun first
fun t_first :: "'a * 'b \<Rightarrow> nat" where
  "t_first pair =
    T_dummy pair + (let (a,b) = dummy pair in T_dummy a)"
lemma "T_first pair = t_first pair"
  by auto

fun comp :: "nat \<Rightarrow> nat" where
  "comp n = (n*5 div 7+1)*0"
lemma comp_simp: "comp n = 0" by simp

text \<open>Should take thm terms as argument for function terms\<close>
time_fun comp equations comp_simp

text \<open>Non recursive function should be without cost for calling the function\<close>
fun divide :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "divide a b = a div b"
time_fun divide
lemma "T_divide a b = 0"
  by simp

text \<open>Should be able to translate functions with function as argument\<close>
fun t_map :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_map f [] = 1"
| "t_map f (x#xs) = 1 + f x + t_map f xs"
time_fun map
lemma [simp,code]:
  "T_map T_f [] = 1"
  "T_map T_f (x21 # x22) = T_f x21 + T_map T_f x22 + 1"
  by (simp_all add: T_map_def)
fun leng :: "'a list \<Rightarrow> nat" where
  "leng [] = 0"
| "leng (x#xs) = Suc (leng xs)"
time_fun leng
lemma leng: "T_leng xs = Suc (length xs)"
  by (induction xs) auto
lemma "T_map T_leng xs = Suc (length xs) + length xs + foldr ((+) o length) xs 0"
  by (induction xs) (auto simp: leng)
lemma "T_map T_leng xs = t_map T_leng xs"
  by (induction xs) auto

text \<open>Functions with function should be called correctly\<close>
fun is_zero :: "nat \<Rightarrow> bool" where "is_zero 0 = True" | "is_zero _ = False"
fun find_zero :: "nat list \<Rightarrow> nat list" where
  "find_zero xs = filter is_zero xs"
time_fun is_zero
time_fun filter
lemma [simp,code]:
  "T_filter T_P [] = 1"
  "T_filter T_P (x # xs) = T_P x + T_filter T_P xs + 1"
  by (simp_all add: T_filter_def)
time_fun find_zero
fun t_is_zero :: "nat \<Rightarrow> nat" where
  "t_is_zero n = 0"
fun t_filter :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_filter _ [] = 1"
| "t_filter t_p (x#xs) = 1 + t_filter t_p xs + t_p x"
lemma filter: "t_filter t_p xs = T_filter t_p xs"
  by (induction xs) auto
fun t_find_zero :: "nat list \<Rightarrow> nat" where
  "t_find_zero xs = t_filter t_is_zero xs"
lemma "t_find_zero xs = T_find_zero xs"
  apply (induction xs)
  using T_is_zero.elims by (auto simp: filter)

fun filter' :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter' _ [] = []"
| "filter' f (x#xs) =
  (case f x of True \<Rightarrow> x # filter' f xs
             | False \<Rightarrow> filter' f xs)"
time_fun filter'

fun I where
  "I x = x"
time_fun I
fun let_test where
  "let_test f x = (let y = f x in I y)"
time_function let_test

text \<open>More functions to test functions as arguments\<close>
fun revmap' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "revmap' f [] ys = ys"
| "revmap' f (x#xs) ys = revmap' f xs (f x # ys)"
fun revmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "revmap f xs = revmap' f xs []"
time_fun revmap'
time_fun revmap
lemma revmap': "T_revmap' (f,T_f) xs ys = Suc (length xs) + foldr ((+) o T_f) xs 0"
  by (induction xs arbitrary: ys) auto
lemma "T_revmap (f,T_f) xs = Suc (length xs) + foldr ((+) o T_f) xs 0"
  by (simp add: revmap')

fun even :: "nat \<Rightarrow> bool"
  and odd :: "nat \<Rightarrow> bool" where
  "even 0 = True"
| "odd 0 = False"
| "even (Suc n) = odd n"
| "odd (Suc n) = even n"
time_fun even odd

text \<open>Let expression where variable is no longer used should be replaced\<close>
fun let_red where
  "let_red x y = (let b = y in let a = x in (a, dummy b))"
time_fun let_red

class T_size =
  fixes T_size :: "'a \<Rightarrow> nat"
instantiation list :: (_) T_size
begin

time_fun length

instance..
end
instantiation nat :: T_size
begin

time_fun "size::nat \<Rightarrow> nat"

instance..
end
lemma "T_size [a,b,c] = 4"
  by simp
lemma "T_size (Suc 4) = 0"
  by simp

fun map2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map2 _ [] = []"
| "map2 f (x#xs) = f x # map2 f xs"
fun t_map2 where
  "t_map2 _ [] = 1"
| "t_map2 (f,T_f) (x#xs) = T_f x + t_map2 (f,T_f) xs + 1"
time_fun [no_simp] map2
lemma "T_map2 f xs = t_map2 f xs"
  by (induction rule: t_map2.induct) auto

locale locTests =
  fixes f :: "'a \<Rightarrow> 'b"
   and  T_f :: "'a \<Rightarrow> nat"
begin

fun simple where
  "simple a = f a"
time_fun simple

fun even :: "'a list \<Rightarrow> 'b list" and odd :: "'a list \<Rightarrow> 'b list" where
  "even [] = []"
| "odd [] = []"
| "even (x#xs) = f x # odd xs"
| "odd (x#xs) = even xs"
time_fun even odd

fun locSum :: "nat list \<Rightarrow> nat" where
  "locSum [] = 0"
| "locSum (x#xs) = x + locSum xs"
time_fun locSum

fun map :: "'a list \<Rightarrow> 'b list" where
  "map [] = []"
| "map (x#xs) = f x # map xs"

fun t_map :: "'a list \<Rightarrow> nat" where
  "t_map [] = 1"
| "t_map (x#xs) = T_f x + t_map xs + 1"

time_fun map
lemma "t_map xs = T_map xs"
  by (induction xs) auto

fun map2 :: "('b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'c list" where
  "map2 _ [] = []"
| "map2 g (x#xs) = g (f x) # map2 g xs"

fun t2_map2 :: "('b \<Rightarrow> 'c) * ('b \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t2_map2 _ [] = 1"
| "t2_map2 g (x#xs) = T_f x + snd g (f x) + t2_map2 g xs + 1"
fun t_map2 :: "('b \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_map2 _ [] = 1"
| "t_map2 T_g (x#xs) = T_f x + T_g (f x) + t_map2 T_g xs + 1"
time_fun map2
lemma "t2_map2 g xs = T2_map2 g xs"
  by (induction xs) auto

lemma T_map2_simps [simp,code]:
  "T_map2 T_uu [] = 1"
  "T_map2 T_g (x # xs) = T_f x + T_g (f x) + T_map2 T_g xs + 1"
  by (simp_all add: T_map2_def)
lemma "t_map2 g xs = T_map2 g xs"
  by (induction xs) auto

end

definition "map_nat xs \<equiv> map (\<lambda>n. 2*n + 1) xs"
definition "t_map_nat xs \<equiv> T_map (\<lambda>n. 0) xs"
time_definition map_nat
lemma "t_map_nat xs = T_map_nat xs"
  by (induction xs) (auto simp: t_map_nat_def)

definition "map2_nat xs \<equiv> map2 (\<lambda>n. 2*n + 1) xs"
definition "t_map2_nat xs \<equiv> T_map2 (\<lambda>n. 2*n+1, \<lambda>n. 0) xs"
time_definition map2_nat
lemma "t_map2_nat xs = T_map2_nat xs"
  by (induction xs) (auto simp: t_map2_nat_def)

definition "let_lambda a b c \<equiv> let lam = (\<lambda>a b. a + b) in lam a (lam b c)"
time_fun let_lambda

datatype testtype = ffff | gggg
locale test1 =
  fixes y::"testtype" and T_y ::"nat"
begin

definition "f_f (x::testtype) = y"
fun join :: "testtype \<Rightarrow> testtype \<Rightarrow> testtype" where
"join ffff gggg = (f_f ffff)"
time_fun f_f
time_fun join

end


datatype return = Reachable | NotReachable
record ('ver, 'neighb) DFS_state = stack:: "'ver list" seen:: "'neighb"  return:: return
time_fun return
time_function seen
time_function stack
locale dfs_test =
  fixes sel::"'neighb \<Rightarrow> 'a" and T_sel::"'neighb \<Rightarrow> nat"
begin

definition "get_state_vertex dfs_state = sel (seen dfs_state)"
time_fun get_state_vertex

definition "get_state_vertex' dfs_state =  
  (case stack dfs_state of
      [] \<Rightarrow> sel (seen dfs_state)
    | Cons _ _ \<Rightarrow> sel (seen dfs_state))"

time_fun get_state_vertex'
end

time_fun take
time_fun drop
fun chop :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "chop 0 _  = []"
| "chop _ [] = []"
| "chop n xs = take n xs # chop n (drop n xs)"
time_fun chop
fun insort1 :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort1 x [] = [x]" |
  "insort1 x (y#ys) =
  (if x \<le> y then x#y#ys else y#(insort1 x ys))"
time_fun insort1
fun insort :: "'a::linorder list \<Rightarrow> 'a list" where
  "insort [] = []" |
  "insort (x#xs) = insort1 x (insort xs)"
time_fun insort
time_fun nth
definition slow_select where
  "slow_select k xs = insort xs ! k"
time_fun slow_select
definition slow_median where
  "slow_median xs = slow_select ((length xs - 1) div 2) xs"
time_fun slow_median
definition partition3 :: "'a \<Rightarrow> 'a :: linorder list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list" where
  "partition3 x xs = (filter (\<lambda>y. y < x) xs, filter (\<lambda>y. y = x) xs, filter (\<lambda>y. y > x) xs)"
time_fun partition3
function mom_select :: "nat \<Rightarrow> 'a :: linorder list \<Rightarrow> 'a" where
   "mom_select k xs = (
      let n = length xs in
      if n \<le> 20 then
        slow_select k xs
      else
        let M = mom_select (((n + 4) div 5 - 1) div 2) (map slow_median (chop 5 xs));
            (ls, es, gs) = partition3 M xs;
            nl = length ls
        in
          if k < nl then mom_select k ls
          else let ne = length es in if k < nl + ne then M
          else mom_select (k - nl - ne) gs
       )"
  by auto
termination sorry
time_function mom_select
termination sorry

partial_function (tailrec) collatz :: "nat \<Rightarrow> bool" where
  "collatz n = (if n \<le> 1 then True
                else if n mod 2 = 0 then collatz (n div 2)
                else collatz (3 * n + 1))"

partial_function (option) T_collatz' :: "nat \<Rightarrow> nat option" where
  "T_collatz' n = (if n \<le> 1 then Some 0
                else if n mod 2 = 0 then Option.bind (T_collatz' (n div 2)) (\<lambda>k. Some (Suc k))
                else Option.bind (T_collatz' (3 * n + 1)) (\<lambda>k. Some (Suc k)))"
time_fun_0 "(mod)"
time_partial_function collatz
lemma setIt: "P i \<Longrightarrow> \<forall>n \<in> {Suc i..j}. P n \<Longrightarrow> \<forall>n \<in> {i..j}. P n"
  by (metis atLeastAtMost_iff le_antisym not_less_eq_eq)
lemma "\<forall>n \<in> {2..20}. T_collatz n = T_collatz' n"
  apply (rule setIt, simp add: T_collatz.simps T_collatz'.simps, simp)+
  by (simp add: T_collatz.simps T_collatz'.simps)

partial_function (tailrec) partdummy :: "nat \<Rightarrow> nat" where
  "partdummy n = dummy n"
definition "user k = partdummy k"
time_partial_function partdummy
time_fun user

end
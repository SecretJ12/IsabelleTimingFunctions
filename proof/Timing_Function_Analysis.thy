theory Timing_Function_Analysis
  imports Main
begin

declare[[syntax_ambiguity_warning=false]]

text \<open>Find better representation of val?\<close>
typedecl val

type_synonym env = "val list"

datatype func = Func string     ("($_)")
datatype pfunc = pFunc string   ("(p$_)")

datatype exp =
    App func "exp list"         ("(_/: _)")
  | pApp pfunc "exp list"       ("(_/: _)")
  | If exp exp exp              ("(IF _/ THEN _/ ELSE _)")
  | Ident nat                   ("(i#_)")
  | Const val                   ("(c#_)")

type_synonym t_pApp = "(string \<Rightarrow> val list \<Rightarrow> val)"
type_synonym defs = "string \<Rightarrow> exp"

locale timing =
  fixes val0 :: val
   and  pApp :: t_pApp
   and  true :: "val \<Rightarrow> bool"
begin
definition false :: "val \<Rightarrow> bool" where "false v \<equiv> \<not> true v"

inductive eval :: "env \<Rightarrow> defs \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> bool" ("(_/ \<turnstile>_/ _/ \<rightarrow> _)") where
Id:   "\<rho> \<turnstile>\<phi> i#i \<rightarrow> (\<rho> ! i)" |
C:    "\<rho> \<turnstile>\<phi> c#v \<rightarrow> v" |
F:    "length es = length vs \<Longrightarrow> (\<And>i. i < length vs \<Longrightarrow> \<rho> \<turnstile>\<phi> (es ! i) \<rightarrow> (vs ! i))
        \<Longrightarrow> \<phi> f = fe \<Longrightarrow> vs \<turnstile>\<phi> fe \<rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<phi> ($f: es) \<rightarrow> v" |
P:    "length es = length vs \<Longrightarrow> (\<And>i. i < length es \<Longrightarrow> \<rho> \<turnstile>\<phi> (es ! i) \<rightarrow> (vs ! i))
        \<Longrightarrow> pApp p vs = v \<Longrightarrow> \<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow> v" |
If1:  "\<rho> \<turnstile>\<phi> c \<rightarrow> v \<Longrightarrow> true v \<Longrightarrow> \<rho> \<turnstile>\<phi> t \<rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF c THEN t ELSE f) \<rightarrow> v" |
If2:  "\<rho> \<turnstile>\<phi> c \<rightarrow> v \<Longrightarrow> false v \<Longrightarrow> \<rho> \<turnstile>\<phi> f \<rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF c THEN t ELSE f) \<rightarrow> v"

inductive_cases IdE[elim!]: "\<rho> \<turnstile>\<phi> i#i \<rightarrow> v"
inductive_cases CE[elim!]: "\<rho> \<turnstile>\<phi> c#v' \<rightarrow> v"
inductive_cases FE[elim!]: "\<rho> \<turnstile>\<phi> ($f: es) \<rightarrow> v"
inductive_cases PE[elim!]: "\<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow> v"
inductive_cases IfE[elim!]: "\<rho> \<turnstile>\<phi> (IF c THEN t ELSE f) \<rightarrow> v"
declare Id[simp]
declare C[simp]
declare F[simp]
declare P[simp]
declare If1[simp]
declare If2[simp]

proposition "\<lbrakk> \<rho> \<turnstile>\<phi> e \<rightarrow> v; \<rho> \<turnstile>\<phi> e \<rightarrow> v' \<rbrakk> \<Longrightarrow> v = v'"
proof (induction arbitrary: v' rule: eval.induct)
  case (F es vs \<rho> \<phi> f fe v)
  then show ?case
    by (metis nth_equalityI FE)
next
  case (P es vs \<rho> \<phi> p v)
  then show ?case by (metis nth_equalityI PE)
qed blast+

fun sum_nat :: "nat list \<Rightarrow> nat" ("\<Sum> _") where
  "sum_nat [] = 0"
| "sum_nat (a#as) = a + sum_nat as"

inductive eval_count :: "env \<Rightarrow> defs \<Rightarrow> exp \<Rightarrow> val * nat \<Rightarrow> bool" ("(_/ \<turnstile>_/ _/ \<rightarrow>s _)") where
cId:   "\<rho> \<turnstile>\<phi> i#i \<rightarrow>s (\<rho>!i,0)" |
cC:    "\<rho> \<turnstile>\<phi> c#v \<rightarrow>s (v,0)" |
cF:    "length es = length vs \<Longrightarrow> length es = length ts
          \<Longrightarrow> (\<And>i. i < length vs \<Longrightarrow> \<rho> \<turnstile>\<phi> (es!i) \<rightarrow>s (vs!i,ts!i))
          \<Longrightarrow> \<phi> f = fe \<Longrightarrow> vs \<turnstile>\<phi> fe \<rightarrow>s (v,t) \<Longrightarrow> \<rho> \<turnstile>\<phi> ($f: es) \<rightarrow>s (v,1+t+\<Sum>ts)" |
cP:    "length es = length vs \<Longrightarrow> (\<And>i. i < length es \<Longrightarrow> \<rho> \<turnstile>\<phi> (es ! i) \<rightarrow>s (vs!i,ts!i))
          \<Longrightarrow> pApp p vs = v \<Longrightarrow> \<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow>s (v,\<Sum>ts)" |
cIf1:  "\<rho> \<turnstile>\<phi> c \<rightarrow>s (v,tc) \<Longrightarrow> true v \<Longrightarrow> \<rho> \<turnstile>\<phi> t \<rightarrow>s (v,tt) \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF c THEN t ELSE f) \<rightarrow>s (v,tc+tt)" |
cIf2:  "\<rho> \<turnstile>\<phi> c \<rightarrow>s (v,tc) \<Longrightarrow> false v \<Longrightarrow> \<rho> \<turnstile>\<phi> f \<rightarrow>s (v,tf) \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF c THEN t ELSE f) \<rightarrow>s (v,tc+tf)"

inductive_cases cIdE[elim!]: "\<rho> \<turnstile>\<phi> i#i \<rightarrow>s v"
inductive_cases cCE[elim!]: "\<rho> \<turnstile>\<phi> c#v' \<rightarrow>s v"
inductive_cases cFE[elim!]: "\<rho> \<turnstile>\<phi> ($f: es) \<rightarrow>s v"
inductive_cases cPE[elim!]: "\<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow>s v"
inductive_cases cIfE[elim!]: "\<rho> \<turnstile>\<phi> (IF c THEN t ELSE f) \<rightarrow>s v"
declare cId[intro]
declare cC[intro]
declare cF[intro]
declare cP[intro]
declare cIf1[intro]
declare cIf2[intro]

thm exI[of _ "[undefined]"]
lemma Ex_list_of_length: "\<exists>xs. length xs = n"
by (rule exI[of _ "replicate n undefined"]) simp

lemma helper:
  assumes "\<And>i. i < length vs \<Longrightarrow> \<exists>t. \<rho> \<turnstile>\<phi> es ! i \<rightarrow>s (vs ! i, t)"
  and "length vs = length es"
  shows  "\<exists>ts. length vs = length ts \<and> (\<forall>i. (i < length vs \<longrightarrow> \<rho> \<turnstile>\<phi> (es!i) \<rightarrow>s (vs!i,ts!i)))"
  using assms
proof (induction vs arbitrary: es)
  case (Cons v vs)
  then obtain e e' where e: "(e#e') = es" by (metis length_Suc_conv)
  with Cons(3) have len: "length e' = length vs" by auto

  from Cons(2) e have "\<And>i. i < length (v#vs) \<Longrightarrow> \<exists>t. \<rho> \<turnstile>\<phi> (e#e') ! i \<rightarrow>s ((v#vs) ! i, t)"
    by blast
  then have "\<And>i. i < length vs \<Longrightarrow> \<exists>t. \<rho> \<turnstile>\<phi> e' ! i \<rightarrow>s (vs ! i, t)"
    by fastforce
  with Cons(1) len
  obtain ts where ts: "length vs = length ts" "\<forall>i<length vs. \<rho> \<turnstile>\<phi> e' ! i \<rightarrow>s (vs ! i, ts ! i)"
    by metis
  from Cons(2) obtain t where t: "\<rho> \<turnstile>\<phi> (es ! 0) \<rightarrow>s ((v # vs) ! 0,t)" by blast

  have "length (v#vs) = length (t#ts)" using len ts by simp
  moreover
  have "\<forall>i<length (v#vs). \<rho> \<turnstile>\<phi> es ! i \<rightarrow>s ((v#vs) ! i, (t#ts) ! i)"
    using ts t e
    by (metis Suc_less_eq length_Cons not0_implies_Suc nth_Cons_0 nth_Cons_Suc)

  ultimately
  show ?case by blast
qed simp

lemma eval_eval_count: "(\<rho> \<turnstile>\<phi> c \<rightarrow> v \<Longrightarrow> \<exists>t. \<rho> \<turnstile>\<phi> c \<rightarrow>s (v,t))"
proof (induction rule: eval.induct)
  case (F es vs \<rho> \<phi> f fe v)
  then show ?case
    by (metis cF helper)
next
  case (P es vs \<rho> \<phi> p v)
  then show ?case
    by (metis cP helper)
qed blast+

lemma eval_count_eval: "\<rho> \<turnstile>\<phi> c \<rightarrow>s (v,t) \<Longrightarrow> \<rho> \<turnstile>\<phi> c \<rightarrow> v"
  by (induction \<rho> \<phi> c "(v,t)" arbitrary: v t rule: eval_count.induct) auto

theorem  eval_eq_eval_count: "(\<rho> \<turnstile>\<phi> c \<rightarrow> v) \<longleftrightarrow> (\<exists>t. \<rho> \<turnstile>\<phi> c \<rightarrow>s (v,t))"
  using eval_count_eval eval_eval_count by auto

end

end
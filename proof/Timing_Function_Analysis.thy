theory Timing_Function_Analysis
  imports Main
begin

declare[[syntax_ambiguity_warning=false]]

text \<open>Find better representation of val?\<close>
type_synonym val = nat

definition false :: "val \<Rightarrow> bool" where "false v \<equiv> v = 0"
definition true :: "val \<Rightarrow> bool" where "true v \<equiv> \<not> false v"

type_synonym env = "val list"

datatype func =
  Func string     ("($_)")
| cFunc func    ("(c$_)")
datatype pfunc = pFunc string   ("(p$_)")

datatype exp =
    App func "exp list"         ("(_/> _)")
  | pApp pfunc "exp list"       ("(_/: _)")
  | If exp exp exp              ("(IF _/ THEN _/ ELSE _)")
  | Ident nat                   ("(i#_)")
  | Const val                   ("(c#_)")

type_synonym defs = "func \<Rightarrow> exp option"

locale timing =
  fixes pApp :: "string \<Rightarrow> val list \<Rightarrow> val"
  assumes sum: "pApp ''sum'' es = sum_list es"
begin

inductive eval :: "env \<Rightarrow> defs \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> bool" ("(_/ \<turnstile>_/ _/ \<rightarrow> _)") where
Id:   "\<rho> \<turnstile>\<phi> i#i \<rightarrow> (\<rho> ! i)" |
C:    "\<rho> \<turnstile>\<phi> c#v \<rightarrow> v" |
F:    "length es = length vs \<Longrightarrow> (\<forall>i < length vs. \<rho> \<turnstile>\<phi> (es ! i) \<rightarrow> (vs ! i))
        \<Longrightarrow> \<phi> f = Some fe \<Longrightarrow> vs \<turnstile>\<phi> fe \<rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<phi> (f> es) \<rightarrow> v" |
P:    "length es = length vs \<Longrightarrow> (\<forall>i < length es. \<rho> \<turnstile>\<phi> (es ! i) \<rightarrow> (vs ! i))
        \<Longrightarrow> pApp p vs = v \<Longrightarrow> \<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow> v" |
If1:  "\<rho> \<turnstile>\<phi> b \<rightarrow> v \<Longrightarrow> true v \<Longrightarrow> \<rho> \<turnstile>\<phi> t \<rightarrow> et \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF b THEN t ELSE f) \<rightarrow> et" |
If2:  "\<rho> \<turnstile>\<phi> b \<rightarrow> v \<Longrightarrow> false v \<Longrightarrow> \<rho> \<turnstile>\<phi> f \<rightarrow> ef \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF b THEN t ELSE f) \<rightarrow> ef"

inductive_cases IdE[elim!]: "\<rho> \<turnstile>\<phi> i#i \<rightarrow> v"
inductive_cases CE[elim!]: "\<rho> \<turnstile>\<phi> c#v' \<rightarrow> v"
inductive_cases FE[elim!]: "\<rho> \<turnstile>\<phi> (f> es) \<rightarrow> v"
inductive_cases PE[elim!]: "\<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow> v"
inductive_cases IfE[elim!]: "\<rho> \<turnstile>\<phi> (IF b THEN t ELSE f) \<rightarrow> v"
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
    by (metis FE list_eq_iff_nth_eq option.inject)
next
  case (P es vs \<rho> \<phi> p v)
  then show ?case by (metis nth_equalityI PE)
next
  case (If1 \<rho> \<phi> b v t et f)
  then show ?case using true_def by blast
next
  case (If2 \<rho> \<phi> b v f ef t)
  then show ?case using true_def by blast
qed blast+

inductive eval_count :: "env \<Rightarrow> defs \<Rightarrow> exp \<Rightarrow> val * nat \<Rightarrow> bool" ("(_/ \<turnstile>_/ _/ \<rightarrow>s _)") where
cId:   "\<rho> \<turnstile>\<phi> i#i \<rightarrow>s (\<rho>!i,0)" |
cC:    "\<rho> \<turnstile>\<phi> c#v \<rightarrow>s (v,0)" |
cF:    "length es = length vs \<Longrightarrow> length es = length ts
          \<Longrightarrow> (\<And>i. i < length vs \<Longrightarrow> \<rho> \<turnstile>\<phi> (es!i) \<rightarrow>s (vs!i,ts!i))
          \<Longrightarrow> \<phi> f = Some fe \<Longrightarrow> vs \<turnstile>\<phi> fe \<rightarrow>s (v,t) \<Longrightarrow> \<rho> \<turnstile>\<phi> (f> es) \<rightarrow>s (v,1+t+sum_list ts)" |
cP:    "length es = length vs \<Longrightarrow> (\<And>i. i < length es \<Longrightarrow> \<rho> \<turnstile>\<phi> (es ! i) \<rightarrow>s (vs!i,ts!i))
          \<Longrightarrow> pApp p vs = v \<Longrightarrow> \<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow>s (v,sum_list ts)" |
cIf1:  "\<rho> \<turnstile>\<phi> b \<rightarrow>s (eb,tb) \<Longrightarrow> true eb \<Longrightarrow> \<rho> \<turnstile>\<phi> t \<rightarrow>s (et,tt)
          \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF b THEN t ELSE f) \<rightarrow>s (et,tb+tt)" |
cIf2:  "\<rho> \<turnstile>\<phi> b \<rightarrow>s (eb,tb) \<Longrightarrow> false eb \<Longrightarrow> \<rho> \<turnstile>\<phi> f \<rightarrow>s (ef,tf)
          \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF b THEN t ELSE f) \<rightarrow>s (ef,tb+tf)"

inductive_cases cIdE[elim!]: "\<rho> \<turnstile>\<phi> i#i \<rightarrow>s v"
inductive_cases cCE[elim!]: "\<rho> \<turnstile>\<phi> c#v' \<rightarrow>s v"
inductive_cases cFE[elim!]: "\<rho> \<turnstile>\<phi> (f> es) \<rightarrow>s v"
inductive_cases cPE[elim!]: "\<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow>s v"
inductive_cases cIfE[elim!]: "\<rho> \<turnstile>\<phi> (IF b THEN t ELSE f) \<rightarrow>s v"
declare cId[intro]
declare cC[intro]
declare cF[intro]
declare cP[intro]
declare cIf1[intro]
declare cIf2[intro]

lemma eval_eval_count':
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

  ultimately show ?case by blast
qed simp

lemma eval_eval_count: "\<rho> \<turnstile>\<phi> b \<rightarrow> v \<Longrightarrow> \<exists>t. \<rho> \<turnstile>\<phi> b \<rightarrow>s (v,t)"
proof (induction rule: eval.induct)
  case (F es vs \<rho> \<phi> f fe v)
  then show ?case
    by (metis cF eval_eval_count')
next
  case (P es vs \<rho> \<phi> p v)
  then show ?case
    by (metis cP eval_eval_count')
qed blast+

lemma eval_count_eval: "\<rho> \<turnstile>\<phi> b \<rightarrow>s (v,t) \<Longrightarrow> \<rho> \<turnstile>\<phi> b \<rightarrow> v"
  by (induction \<rho> \<phi> b "(v,t)" arbitrary: v t rule: eval_count.induct) auto

theorem  eval_eq_eval_count: "(\<rho> \<turnstile>\<phi> b \<rightarrow> v) \<longleftrightarrow> (\<exists>t. \<rho> \<turnstile>\<phi> b \<rightarrow>s (v,t))"
  using eval_count_eval eval_eval_count by auto

(* TODO: define T and proove:
proposition "\<rho> \<turnstile>\<phi> e \<rightarrow>s (v,t) \<longleftrightarrow> \<rho> \<turnstile>\<phi> e \<rightarrow> v \<and> T \<Delta> = t"
*)

fun \<T> :: "exp \<Rightarrow> exp" where
  "\<T> c#v = c#0"
| "\<T> i#i = c#0"
| "\<T> (IF b THEN t ELSE f) = p$''sum'': [\<T> b, IF b THEN \<T> t ELSE \<T> f]"
| "\<T> (p$_: args) = p$''sum'': map \<T> args"
| "\<T> (f> args) = p$''sum'': (c$f> args # map \<T> args)"

fun c :: "exp \<Rightarrow> exp" where
  "c e = p$''sum'': [c#1, \<T> e]"

fun conv :: "defs \<Rightarrow> defs" where
  "conv \<phi> (c$f) = (case \<phi> f of None \<Rightarrow> None | Some e \<Rightarrow> Some (c e))"
| "conv \<phi> ($f) = \<phi> $f"

definition defs_cor where
  "defs_cor \<phi> =
  (\<forall>f. (case \<phi> f of Some e \<Rightarrow> \<phi> (c$f) = None \<or> \<phi> (c$f) = Some (c e)
                  | None \<Rightarrow> \<phi> (c$f) = None))"

lemma conv_trans: "defs_cor \<phi> \<Longrightarrow> \<phi> f = Some e \<Longrightarrow> (conv \<phi>) f = Some e"
  apply (cases f)
  by auto (smt (verit, best) conv.simps(1) defs_cor_def option.case_eq_if option.distinct(1))

lemma eval_conv_trans: "\<rho> \<turnstile>\<phi> e \<rightarrow> v \<Longrightarrow> defs_cor \<phi> \<Longrightarrow> \<rho> \<turnstile>(conv \<phi>) e \<rightarrow> v"
  by (induction rule: eval.induct) (auto simp: conv_trans)

theorem
  assumes "\<rho> \<turnstile>\<phi> e \<rightarrow>s (s,t)"
    and   "defs_cor \<phi>"
  shows  "\<rho> \<turnstile>(conv \<phi>) (\<T> e) \<rightarrow> t"
  using assms
proof (induction \<rho> \<phi> e "(s,t)" arbitrary: s t rule: eval_count.induct)
  case (cF es vs ts \<rho> \<phi> f fe v t)
  then show ?case sorry
next
  case (cP es vs \<rho> \<phi> ts p v)
  then show ?case sorry
next
  case (cIf1 \<rho> \<phi> b eb tb t et tt f)

  let ?ts = "[\<T> b, IF b THEN \<T> t ELSE \<T> f]"

  have "\<rho> \<turnstile>\<phi> b \<rightarrow> eb"
    using cIf1(1) eval_count_eval by auto

  then have b: "\<rho> \<turnstile>(conv \<phi>) b \<rightarrow> eb"
    using cIf1.prems eval_conv_trans by auto

  from b cIf1(3) cIf1(5)
  have ifelse: "\<rho> \<turnstile>(conv \<phi>) IF b THEN \<T> t ELSE \<T> f \<rightarrow> tt"
    by (simp add: cIf1.prems)

  from cIf1(2) ifelse
  have args: "(\<forall>i < length ?ts. \<rho> \<turnstile>(conv \<phi>) (?ts ! i) \<rightarrow> ([tb,tt] ! i))"
    by (simp add: cIf1.prems nth_Cons')
  have app: "pApp ''sum'' [tb,tt] = tb + tt" by (simp add: timing.sum timing_axioms)

  from args app P[of ?ts "[tb,tt]"]
  have "\<rho> \<turnstile>conv \<phi> (p$''sum'': ?ts) \<rightarrow> tb + tt" by simp
  then show ?case by simp
next
  case (cIf2 \<rho> \<phi> b eb tb f ef tf t)

  let ?ts = "[\<T> b, IF b THEN \<T> t ELSE \<T> f]"

  have "\<rho> \<turnstile>\<phi> b \<rightarrow> eb"
    using cIf2(1) eval_count_eval by auto

  then have b: "\<rho> \<turnstile>(conv \<phi>) b \<rightarrow> eb"
    using cIf2.prems eval_conv_trans by auto

  from b cIf2(3) cIf2(5)
  have ifelse: "\<rho> \<turnstile>(conv \<phi>) IF b THEN \<T> t ELSE \<T> f \<rightarrow> tf"
    by (simp add: cIf2.prems)

  from cIf2(2) ifelse
  have args: "(\<forall>i < length ?ts. \<rho> \<turnstile>(conv \<phi>) (?ts ! i) \<rightarrow> ([tb,tf] ! i))"
    by (simp add: cIf2.prems nth_Cons')
  have app: "pApp ''sum'' [tb,tf] = tb + tf" by (simp add: timing.sum timing_axioms)

  from args app P[of ?ts "[tb,tf]"]
  have "\<rho> \<turnstile>conv \<phi> (p$''sum'': ?ts) \<rightarrow> tb + tf" by simp
  then show ?case by simp
qed simp+

end

end
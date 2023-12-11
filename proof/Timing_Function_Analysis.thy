theory Timing_Function_Analysis
  imports Main
begin

declare[[syntax_ambiguity_warning=false]]

text \<open>Formalization of David Sands' "Calculi for time analysis of functional programs"
      Chapter 2 "Computational-Models and Cost-Functions"\<close>

text \<open>Assuming the model to works under natural numbers.\<close>
typedecl typs
datatype val = N nat | Ty typs
fun val_to_nat :: "val \<Rightarrow> nat" where
  "val_to_nat (N n) = n"

definition false :: "val \<Rightarrow> bool" where "false v \<equiv> v = N 0"
definition true :: "val \<Rightarrow> bool" where "true v \<equiv> \<not> false v"

text \<open>Definition of functions and primary functions\<close>
datatype func =
  Func string     ("($_)")
| cFunc func    ("(c$_)")
datatype pfunc = pFunc string   ("(p$_)")

text \<open>Defines simple expression\<close>
datatype exp =
    App func "exp list"         ("(_/> _)")
  | pApp pfunc "exp list"       ("(_/: _)")
  | If exp exp exp              ("(IF _/ THEN _/ ELSE _)")
  | Ident nat                   ("(i#_)")
  | Const val                   ("(c#_)")

text \<open>env represents local variables in a expression / function\<close>
type_synonym env = "val list"
text \<open>defs contains all the functions defined\<close>
type_synonym defs = "func \<Rightarrow> exp option"

text \<open>Exact set of primitive functions is unspecified,
      Sand assumes arithmetic and boolean functions as well as list constructor.
      For simplicity we only assume sum here.\<close>
axiomatization pApp :: "string \<Rightarrow> val list \<Rightarrow> val" where
  sum: "pApp ''sum'' es = (N o sum_list o map val_to_nat) es"

text \<open>The syntax \<rho> \<turnstile>\<phi> e \<rightarrow> v reads as
  "Given environment \<rho>, in the context of definitions \<phi> expression e evaluates to value v"\<close>
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

text \<open>Prove that semantic describes deterministic computation\<close>
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

text \<open>Defines step-counting Semantics.
      Evaluates as eval, but additionally counts the number of applications of non-primitive functions\<close>
inductive eval_count :: "env \<Rightarrow> defs \<Rightarrow> exp \<Rightarrow> val * nat \<Rightarrow> bool" ("(_/ \<turnstile>_/ _/ \<rightarrow>s _)") where
cId:   "\<rho> \<turnstile>\<phi> i#i \<rightarrow>s (\<rho>!i,0)" |
cC:    "\<rho> \<turnstile>\<phi> c#v \<rightarrow>s (v,0)" |
cF:    "length es = length vs \<Longrightarrow> length es = length ts
          \<Longrightarrow> (\<And>i. i < length vs \<Longrightarrow> \<rho> \<turnstile>\<phi> (es!i) \<rightarrow>s (vs!i,ts!i))
          \<Longrightarrow> \<phi> f = Some fe \<Longrightarrow> vs \<turnstile>\<phi> fe \<rightarrow>s (v,t) \<Longrightarrow> \<rho> \<turnstile>\<phi> (f> es) \<rightarrow>s (v,1+t+sum_list ts)" |
cP:    "length es = length vs \<Longrightarrow> length es = length ts \<Longrightarrow> (\<And>i. i < length es \<Longrightarrow> \<rho> \<turnstile>\<phi> (es ! i) \<rightarrow>s (vs!i,ts!i))
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

text \<open>Show that computation result of eval and eval_count is equal\<close>
theorem  eval_eq_eval_count: "(\<rho> \<turnstile>\<phi> b \<rightarrow> v) \<longleftrightarrow> (\<exists>t. \<rho> \<turnstile>\<phi> b \<rightarrow>s (v,t))"
  using eval_count_eval eval_eval_count by auto

text \<open>\<T> constructs the cost function for an expression\<close>
fun \<T> :: "exp \<Rightarrow> exp" where
  "\<T> c#v = c#N 0"
| "\<T> i#i = c#N 0"
| "\<T> (IF b THEN t ELSE f) = p$''sum'': [\<T> b, IF b THEN \<T> t ELSE \<T> f]"
| "\<T> (p$_: args) = p$''sum'': map \<T> args"
| "\<T> (f> args) = p$''sum'': (c$f> args # map \<T> args)"

text \<open>c constructs the cost function for a function given by its expression\<close>
fun c :: "exp \<Rightarrow> exp" where
  "c e = p$''sum'': [c#N 1, \<T> e]"

text \<open>Adds cost functions for existing functions in a definition\<close>
fun conv :: "defs \<Rightarrow> defs" where
  "conv \<phi> (c$f) = (case \<phi> f of None \<Rightarrow> None | Some e \<Rightarrow> Some (c e))"
| "conv \<phi> ($f) = \<phi> $f"

text \<open>A definition is correct if each cost function fits to its function\<close>
definition defs_cor where
  "defs_cor \<phi> =
  (\<forall>f. (case \<phi> f of Some e \<Rightarrow> \<phi> (c$f) = None \<or> \<phi> (c$f) = Some (c e)
                  | None \<Rightarrow> \<phi> (c$f) = None))"

lemma conv_trans: "defs_cor \<phi> \<Longrightarrow> \<phi> f = Some e \<Longrightarrow> (conv \<phi>) f = Some e"
  apply (induction f arbitrary: e)
  by auto (smt (verit, del_insts) case_optionE defs_cor_def option.case_eq_if option.distinct(1))

lemma eval_conv_trans: "\<rho> \<turnstile>\<phi> e \<rightarrow> v \<Longrightarrow> defs_cor \<phi> \<Longrightarrow> \<rho> \<turnstile>(conv \<phi>) e \<rightarrow> v"
  by (induction rule: eval.induct) (auto simp: conv_trans)

text \<open>Prove correctness theorem that the converted expression with converted definitions
      evaluates to the same result as the evaluated by the step counting semantic\<close>
theorem conv_cor:
  assumes "\<rho> \<turnstile>\<phi> e \<rightarrow>s (s,t)"
    and   "defs_cor \<phi>"
   shows  "\<rho> \<turnstile>(conv \<phi>) (\<T> e) \<rightarrow> N t"
  using assms
proof (induction \<rho> \<phi> e "(s,t)" arbitrary: s t rule: eval_count.induct)
  case (cF es vs ts \<rho> \<phi> f fe v t)

  obtain ts' where ts: "ts' = map N ts" by simp
  then have papp: "pApp ''sum'' (N (1 + t) # ts') = N (1 + t + sum_list ts)"
    by (simp add: comp_def sum)
  
  from P[of "[c#N 1, \<T> fe]" "[N 1,N t]" vs "conv \<phi>" "''sum''" "N (1+t)"] cF.hyps(7) cF.prems sum
  have "vs \<turnstile>conv \<phi> p$''sum'': [c#N 1, \<T> fe] \<rightarrow> N (1 + t)"
    by (simp add: nth_Cons')
  then have c_fe: "vs \<turnstile>conv \<phi> (c fe) \<rightarrow> N (1 + t)" by simp

  from cF.hyps(3) cF.prems eval_conv_trans eval_eq_eval_count
  have "\<forall>i<length vs. \<rho> \<turnstile>conv \<phi> es ! i \<rightarrow> vs ! i" by blast

  with cF(1) cF(5) c_fe F[of es vs \<rho> "conv \<phi>" "c$f" "c fe" "N (1+t)"]
  have "\<rho> \<turnstile>conv \<phi> c$f> es \<rightarrow> N (1 + t)" by simp

  with cF.hyps(1) cF.hyps(4) cF.prems ts cF.hyps(2)
  have "\<forall>i<length (c$f> es # map \<T> es). \<rho> \<turnstile>conv \<phi> (c$f> es # map \<T> es) ! i \<rightarrow> ((N (1 + t)) # ts') ! i"
    by (simp add: nth_Cons')

  with cF.hyps(2) sum papp ts
    P[of "c$f> es # map \<T> es" "(N (1+t)) # ts'" \<rho> "conv \<phi>" "''sum''" "N (1 + t + sum_list ts)"]
  show ?case
    by simp
next
  case (cP es vs ts \<rho> \<phi> p v)
  
  obtain ts' where ts: "ts' = map N ts" by blast
  then have papp: "pApp ''sum'' ts' = N (sum_list ts)"
    by (simp add: comp_def sum)

  with ts cP sum P[of "map \<T> es" ts' \<rho> "conv \<phi>" "''sum''" "(N o sum_list o map val_to_nat) ts'"(*"map val_to_nat ts" \<rho> "conv \<phi>" "''sum''" "(sum_list) ts"*)]
  show ?case
    by simp
next
  case (cIf1 \<rho> \<phi> b eb tb t et tt f)

  let ?ts = "[\<T> b, IF b THEN \<T> t ELSE \<T> f]"

  have "\<rho> \<turnstile>\<phi> b \<rightarrow> eb"
    using cIf1(1) eval_count_eval by auto

  then have b: "\<rho> \<turnstile>(conv \<phi>) b \<rightarrow> eb"
    using cIf1.prems eval_conv_trans by auto

  from b cIf1(3) cIf1(5)
  have ifelse: "\<rho> \<turnstile>(conv \<phi>) IF b THEN \<T> t ELSE \<T> f \<rightarrow> N tt"
    by (simp add: cIf1.prems)

  from cIf1(2) ifelse
  have args: "(\<forall>i < length ?ts. \<rho> \<turnstile>(conv \<phi>) (?ts ! i) \<rightarrow> ([N tb,N tt] ! i))"
    by (simp add: cIf1.prems nth_Cons')
  have app: "pApp ''sum'' [N tb,N tt] = N (tb + tt)" by (simp add: sum)

  from args app P[of ?ts "[N tb,N tt]"]
  have "\<rho> \<turnstile>conv \<phi> (p$''sum'': ?ts) \<rightarrow> N (tb + tt)" by simp
  then show ?case by simp
next
  case (cIf2 \<rho> \<phi> b eb tb f ef tf t)

  let ?ts = "[\<T> b, IF b THEN \<T> t ELSE \<T> f]"

  have "\<rho> \<turnstile>\<phi> b \<rightarrow> eb"
    using cIf2(1) eval_count_eval by auto

  then have b: "\<rho> \<turnstile>(conv \<phi>) b \<rightarrow> eb"
    using cIf2.prems eval_conv_trans by auto

  from b cIf2(3) cIf2(5)
  have ifelse: "\<rho> \<turnstile>(conv \<phi>) IF b THEN \<T> t ELSE \<T> f \<rightarrow> N tf"
    by (simp add: cIf2.prems)

  from cIf2(2) ifelse
  have args: "(\<forall>i < length ?ts. \<rho> \<turnstile>(conv \<phi>) (?ts ! i) \<rightarrow> ([N tb,N tf] ! i))"
    by (simp add: cIf2.prems nth_Cons')
  have app: "pApp ''sum'' [N tb,N tf] = N (tb + tf)" by (simp add: sum)

  from args app P[of ?ts "[N tb,N tf]"]
  have "\<rho> \<turnstile>conv \<phi> (p$''sum'': ?ts) \<rightarrow> N (tb + tf)" by simp
  then show ?case by simp
qed simp+

text \<open>Defines a simple variant of correct definitions: no existing timing functions\<close>
definition no_time where
  "no_time \<phi> = (\<forall>f. \<phi> c$f = None)"

lemma no_time_defs_cor: "no_time \<phi> \<Longrightarrow> defs_cor \<phi>"
  by (simp add: defs_cor_def no_time_def option.case_eq_if)

corollary conv_cor_no_time:
  assumes "\<rho> \<turnstile>\<phi> e \<rightarrow>s (s,t)"
    and   "no_time \<phi>"
   shows  "\<rho> \<turnstile>(conv \<phi>) (\<T> e) \<rightarrow> N t"
  using assms conv_cor no_time_defs_cor by auto

end
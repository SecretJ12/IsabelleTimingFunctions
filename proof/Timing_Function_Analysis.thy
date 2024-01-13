theory Timing_Function_Analysis
  imports Main
begin

declare[[syntax_ambiguity_warning=false]]

text \<open>Formalization of David Sands' "Calculi for time analysis of functional programs"
      Chapter 2 "Computational-Models and Cost-Functions"\<close>

text \<open>Assuming the model to works under natural numbers.\<close>
typedecl "value"
datatype val = N nat | V "value"
fun val_to_nat :: "val \<Rightarrow> nat" where
  "val_to_nat (N n) = n"

definition false :: "val \<Rightarrow> bool" where "false v \<equiv> v = N 0"
definition true :: "val \<Rightarrow> bool" where "true v \<equiv> \<not> false v"

text \<open>Definition of functions and primary functions\<close>
datatype funId =
  Fun string
| cFun string
datatype pfunId = pFun string

text \<open>Defines simple expression\<close>
datatype exp =
    App funId "exp list"        (infix "$" 100)
  | pApp pfunId "exp list"      (infix "$$" 100)
  | If exp exp exp              ("(IF _/ THEN _/ ELSE _)")
  | Ident nat
  | Const val

text \<open>env represents local variables in a expression / function\<close>
type_synonym env = "val list"
text \<open>defs contains all the functions defined\<close>
type_synonym defs = "funId \<Rightarrow> exp option"

text \<open>Exact set of primitive functions is unspecified,
      Sand assumes arithmetic and boolean functions as well as list constructor.
      For simplicity we only assume sum here.\<close>
axiomatization pApp :: "string \<Rightarrow> val list \<Rightarrow> val" where
  sum: "pApp ''sum'' es = (N o sum_list o map val_to_nat) es"

text \<open>The syntax \<rho>, \<phi> \<turnstile> e \<rightarrow> v reads as
  "Given environment \<rho>, in the context of definitions \<phi> expression e evaluates to value v"\<close>
inductive eval :: "env \<Rightarrow> defs \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> bool" ("(_/, _/ \<turnstile>_/ \<rightarrow> _)") where
Id:   "\<rho>, \<phi> \<turnstile> Ident i \<rightarrow> (\<rho> ! i)" |
C:    "\<rho>, \<phi> \<turnstile> Const v \<rightarrow> v" |
F:    "length es = length vs \<Longrightarrow> (\<forall>i < length vs. \<rho>, \<phi> \<turnstile> (es ! i) \<rightarrow> (vs ! i))
        \<Longrightarrow> \<phi> f = Some fe \<Longrightarrow> vs, \<phi> \<turnstile> fe \<rightarrow> v \<Longrightarrow> \<rho>, \<phi> \<turnstile> (f$ es) \<rightarrow> v" |
P:    "length es = length vs \<Longrightarrow> (\<forall>i < length es. \<rho>, \<phi> \<turnstile> (es ! i) \<rightarrow> (vs ! i))
        \<Longrightarrow> pApp p vs = v \<Longrightarrow> \<rho>, \<phi> \<turnstile> (pFun p$$ es) \<rightarrow> v" |
If1:  "\<rho>, \<phi> \<turnstile> b \<rightarrow> v \<Longrightarrow> true v \<Longrightarrow> \<rho>, \<phi> \<turnstile> t \<rightarrow> et \<Longrightarrow> \<rho>, \<phi> \<turnstile> (IF b THEN t ELSE f) \<rightarrow> et" |
If2:  "\<rho>, \<phi> \<turnstile> b \<rightarrow> v \<Longrightarrow> false v \<Longrightarrow> \<rho>, \<phi> \<turnstile> f \<rightarrow> ef \<Longrightarrow> \<rho>, \<phi> \<turnstile> (IF b THEN t ELSE f) \<rightarrow> ef"

inductive_cases IdE[elim!]: "\<rho>, \<phi> \<turnstile> Ident i \<rightarrow> v"
inductive_cases CE[elim!]: "\<rho>, \<phi> \<turnstile> Const v' \<rightarrow> v"
inductive_cases FE[elim!]: "\<rho>, \<phi> \<turnstile> (f$ es) \<rightarrow> v"
inductive_cases PE[elim!]: "\<rho>, \<phi> \<turnstile> (pFun p$$ es) \<rightarrow> v"
inductive_cases IfE[elim!]: "\<rho>, \<phi> \<turnstile> (IF b THEN t ELSE f) \<rightarrow> v"
declare eval.intros[simp]

text \<open>Prove that semantic describes deterministic computation\<close>
proposition "\<lbrakk> \<rho>, \<phi> \<turnstile> e \<rightarrow> v; \<rho>, \<phi> \<turnstile> e \<rightarrow> v' \<rbrakk> \<Longrightarrow> v = v'"
proof (induction arbitrary: v' rule: eval.induct)
  case (F es vs \<rho> \<phi> f fe v)
  then show ?case
    by (metis FE list_eq_iff_nth_eq option.inject)
next
  case (P es vs \<rho> \<phi> p v)
  then show ?case
    by (metis nth_equalityI PE)
next
  case (If1 \<rho> \<phi> b v t et f)
  then show ?case using true_def by blast
next
  case (If2 \<rho> \<phi> b v f ef t)
  then show ?case using true_def by blast
qed blast+

text \<open>Defines step-counting Semantics.
      Evaluates as eval, but additionally counts the number of applications of non-primitive functions\<close>
inductive eval_count :: "env \<Rightarrow> defs \<Rightarrow> exp \<Rightarrow> val * nat \<Rightarrow> bool" ("(_/, _/ \<turnstile> _/ \<rightarrow>s _)") where
cId:   "\<rho>, \<phi> \<turnstile> Ident i \<rightarrow>s (\<rho>!i,0)" |
cC:    "\<rho>, \<phi> \<turnstile> Const v \<rightarrow>s (v,0)" |
cF:    "length es = length vs \<Longrightarrow> length es = length ts
          \<Longrightarrow> (\<forall>i < length vs. \<rho>, \<phi> \<turnstile> (es!i) \<rightarrow>s (vs!i,ts!i))
          \<Longrightarrow> \<phi> f = Some fe \<Longrightarrow> vs, \<phi> \<turnstile> fe \<rightarrow>s (v,t) \<Longrightarrow> \<rho>, \<phi> \<turnstile> (f$ es) \<rightarrow>s (v,1+t+sum_list ts)" |
cP:    "length es = length vs \<Longrightarrow> length es = length ts \<Longrightarrow> (\<forall>i < length es. \<rho>, \<phi> \<turnstile> (es ! i) \<rightarrow>s (vs!i,ts!i))
          \<Longrightarrow> pApp p vs = v \<Longrightarrow> \<rho>, \<phi> \<turnstile> (pFun p$$ es) \<rightarrow>s (v,sum_list ts)" |
cIf1:  "\<rho>, \<phi> \<turnstile> b \<rightarrow>s (eb,tb) \<Longrightarrow> true eb \<Longrightarrow> \<rho>, \<phi> \<turnstile> t \<rightarrow>s (et,tt)
          \<Longrightarrow> \<rho>, \<phi> \<turnstile> (IF b THEN t ELSE f) \<rightarrow>s (et,tb+tt)" |
cIf2:  "\<rho>, \<phi> \<turnstile> b \<rightarrow>s (eb,tb) \<Longrightarrow> false eb \<Longrightarrow> \<rho>, \<phi> \<turnstile> f \<rightarrow>s (ef,tf)
          \<Longrightarrow> \<rho>, \<phi> \<turnstile> (IF b THEN t ELSE f) \<rightarrow>s (ef,tb+tf)"

inductive_cases cIdE[elim!]: "\<rho>, \<phi> \<turnstile> Ident i \<rightarrow>s v"
inductive_cases cCE[elim!]: "\<rho>, \<phi> \<turnstile> Const v' \<rightarrow>s v"
inductive_cases cFE[elim!]: "\<rho>, \<phi> \<turnstile> (f$ es) \<rightarrow>s v"
inductive_cases cPE[elim!]: "\<rho>, \<phi> \<turnstile> (pFun p$$ es) \<rightarrow>s v"
inductive_cases cIfE[elim!]: "\<rho>, \<phi> \<turnstile> (IF b THEN t ELSE f) \<rightarrow>s v"
declare eval_count.intros[intro]

lemma eval_count_eval: "\<rho>, \<phi> \<turnstile> b \<rightarrow>s (v,t) \<Longrightarrow> \<rho>, \<phi> \<turnstile> b \<rightarrow> v"
  by (induction \<rho> \<phi> b "(v,t)" arbitrary: v t rule: eval_count.induct) auto

lemma eval_eval_count':
  assumes "\<forall>i < length vs. \<exists>t. \<rho>, \<phi> \<turnstile> es ! i \<rightarrow>s (vs ! i, t)"
  and "length es = length vs"
  shows  "\<exists>ts. length vs = length ts \<and> (\<forall>i. (i < length vs \<longrightarrow> \<rho>, \<phi> \<turnstile> (es!i) \<rightarrow>s (vs!i,ts!i)))"
  using assms
proof (induction vs arbitrary: es)
  case (Cons v vs)
  then obtain e e' where e: "(e#e') = es" by (metis length_Suc_conv)
  with Cons(3) have len: "length e' = length vs" by auto

  from Cons(2) e have "\<forall>i < length vs. \<exists>t. \<rho>, \<phi> \<turnstile> e' ! i \<rightarrow>s (vs ! i, t)"
    by fastforce
  from Cons(1)[OF this len]
  obtain ts where ts: "length vs = length ts" "\<forall>i<length vs. \<rho>, \<phi> \<turnstile> e' ! i \<rightarrow>s (vs ! i, ts ! i)"
    by blast
  from Cons(2) obtain t where t: "\<rho>, \<phi> \<turnstile> (es ! 0) \<rightarrow>s ((v # vs) ! 0,t)" by blast

  have "length (v#vs) = length (t#ts)" using len ts by simp
  moreover
  have "\<forall>i<length (v#vs). \<rho>, \<phi> \<turnstile> es ! i \<rightarrow>s ((v#vs) ! i, (t#ts) ! i)"
    using ts(2) t e
    by (metis Suc_less_eq length_Cons not0_implies_Suc nth_Cons_0 nth_Cons_Suc)

  ultimately show ?case by blast
qed simp

lemma eval_eval_count: "\<rho>, \<phi> \<turnstile> b \<rightarrow> v \<Longrightarrow> \<exists>t. \<rho>, \<phi> \<turnstile> b \<rightarrow>s (v,t)"
proof (induction rule: eval.induct)
  case (F es vs \<rho> \<phi> f fe v)
  then show ?case
    by (metis cF eval_eval_count')
next
  case (P es vs \<rho> \<phi> p v)
  then show ?case
    by (metis cP eval_eval_count')
qed blast+

text \<open>Show that computation result of eval and eval_count is equal\<close>
theorem eval_eq_eval_count: "(\<rho>, \<phi> \<turnstile> b \<rightarrow> v) \<longleftrightarrow> (\<exists>t. \<rho>, \<phi> \<turnstile> b \<rightarrow>s (v,t))"
  using eval_count_eval eval_eval_count by auto

text \<open>\<T> constructs the cost function for an expression\<close>
fun \<T> :: "exp \<Rightarrow> exp" where
  "\<T> (Const v) = Const (N 0)"
| "\<T> (Ident i) = Const (N 0)"
| "\<T> (IF b THEN t ELSE f) = pFun ''sum''$$ [\<T> b, IF b THEN \<T> t ELSE \<T> f]"
| "\<T> (pFun _$$ args) = pFun ''sum''$$ map \<T> args"
| "\<T> (Fun f$ args) = pFun ''sum''$$ (cFun f$ args # map \<T> args)"

text \<open>cost constructs the cost function for a function given by its expression\<close>
definition cost :: "exp \<Rightarrow> exp" where
  "cost e = pFun ''sum''$$ [Const (N 1), \<T> e]"

text \<open>Adds cost functions for existing functions in a definition\<close>
fun conv :: "defs \<Rightarrow> defs" where
  "conv \<phi> (Fun f) = \<phi> (Fun f)"
| "conv \<phi> (cFun f) = (case \<phi> (Fun f) of None \<Rightarrow> None | Some e \<Rightarrow> Some (cost e))"

text \<open>Defines premise for definitions without timing functions\<close>
definition no_time where
  "no_time \<phi> = (\<forall>f. \<phi> (cFun f) = None)"

lemma no_time_trans: "no_time \<phi> \<Longrightarrow> \<phi> f = Some e \<Longrightarrow> (conv \<phi>) f = Some e"
  by (induction f arbitrary: e) (auto simp: no_time_def)
lemma eval_no_time_trans: "\<rho>, \<phi> \<turnstile> e \<rightarrow> v \<Longrightarrow> no_time \<phi> \<Longrightarrow> \<rho>, (conv \<phi>) \<turnstile> e \<rightarrow> v"
  by (induction rule: eval.induct) (auto simp: no_time_trans)

text \<open>Prove correctness theorem that the converted expression with converted definitions
      evaluates to the same result as the evaluated by the step counting semantic\<close>
theorem conv_cor:
  assumes "\<rho>, \<phi> \<turnstile> e \<rightarrow>s (s,t)"
    and   "no_time \<phi>"
   shows  "\<rho>, (conv \<phi>) \<turnstile> (\<T> e) \<rightarrow> N t"
  using assms
proof (induction \<rho> \<phi> e "(s,t)" arbitrary: s t rule: eval_count.induct)
  case (cF es vs ts \<rho> \<phi> f fe v t)

  from cF(4) cF(5) cF(7)
  obtain fn where f_fn: "f = Fun fn"
    by (cases f) (auto simp: no_time_def)

  obtain ts' where ts: "ts' = map N ts" by simp
  then have papp: "pApp ''sum'' (N (1 + t) # ts') = N (1 + t + sum_list ts)"
    by (simp add: comp_def sum)
  
  from P[of "[Const (N 1), \<T> fe]" "[N 1,N t]" vs "conv \<phi>" "''sum''" "N (1+t)"] cF.hyps(6)[OF cF.prems] sum
  have c_fe: "vs, conv \<phi> \<turnstile> cost fe \<rightarrow> N (1 + t)"
    by (simp add: nth_Cons' cost_def)

  from cF.hyps(3) eval_no_time_trans[OF _ cF.prems] eval_eq_eval_count
  have "\<forall>i<length vs. \<rho>, conv \<phi> \<turnstile> es ! i \<rightarrow> vs ! i" by blast

  with cF(1) cF(4) c_fe f_fn
  have "\<rho>, conv \<phi> \<turnstile> cFun fn$ es \<rightarrow> N (1 + t)" by simp

  with cF(1) cF(2) cF(3) cF(7) ts
  have "\<forall>i<length (cFun fn$ es # map \<T> es). \<rho>, conv \<phi> \<turnstile> (cFun fn$ es # map \<T> es) ! i \<rightarrow> ((N (1 + t)) # ts') ! i"
    by (simp add: nth_Cons')

  from cF(2) sum ts f_fn
    P[OF _ this papp]
  show ?case by simp
next
  case (cP es vs ts \<rho> \<phi> p v)
  
  obtain ts' where ts: "ts' = map N ts" by blast
  then have "pApp ''sum'' ts' = N (sum_list ts)"
    by (simp add: comp_def sum)

  with ts cP(2) cP(3) cP(5) sum
  P[of "map \<T> es" ts' \<rho> "conv \<phi>" "''sum''" "(N o sum_list o map val_to_nat) ts'"]
  show ?case
    by simp
next
  case (cIf1 \<rho> \<phi> b eb tb t et tt f)

  let ?ts = "[\<T> b, IF b THEN \<T> t ELSE \<T> f]"

  from cIf1(2)[OF cIf1.prems]
    If1[OF eval_no_time_trans[OF eval_count_eval[OF cIf1(1)] cIf1.prems] cIf1(3) cIf1(5)[OF cIf1.prems]]
  have args: "(\<forall>i < length ?ts. \<rho>, conv \<phi> \<turnstile> (?ts ! i) \<rightarrow> ([N tb,N tt] ! i))"
    by (simp add: nth_Cons')
  have app: "pApp ''sum'' [N tb,N tt] = N (tb + tt)" by (simp add: sum)

  from sum P[OF _ args app]
  show ?case by simp
next
  case (cIf2 \<rho> \<phi> b eb tb f ef tf t)

  let ?ts = "[\<T> b, IF b THEN \<T> t ELSE \<T> f]"

  from cIf2(2)[OF cIf2.prems]
    If2[OF eval_no_time_trans[OF eval_count_eval[OF cIf2(1)] cIf2.prems] cIf2(3) cIf2(5)[OF cIf2.prems]]
  have args: "(\<forall>i < length ?ts. \<rho>, conv \<phi> \<turnstile> (?ts ! i) \<rightarrow> ([N tb,N tf] ! i))"
    by (simp add: nth_Cons')
  have app: "pApp ''sum'' [N tb,N tf] = N (tb + tf)" by (simp add: sum)

  from sum P[OF _ args app]
  show ?case by simp
qed simp+

end
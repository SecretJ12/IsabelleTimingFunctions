theory Timing_Function_Analysis
  imports Main
begin

declare[[syntax_ambiguity_warning=false]]

text \<open>Find better representation of val?\<close>
type_synonym val = int
definition false :: "val \<Rightarrow> bool" where "false v \<equiv> v = 0"
definition true :: "val \<Rightarrow> bool" where "true v \<equiv> \<not>false v"

type_synonym env = "val list"

datatype func = Func string     ("($_)")
datatype pfunc = pFunc string   ("(p$_)")

datatype exp =
    App func "exp list"         ("(_/: _)")
  | pApp pfunc "exp list"       ("(_/: _)")
  | If exp exp exp              ("(IF _/ THEN _/ ELSE _)")
  | Ident nat                   ("(#_)")
  | Const val                   ("(c#_)")

type_synonym pApp = "(string \<Rightarrow> val list \<Rightarrow> val)"
type_synonym defs = "string \<Rightarrow> exp"

definition null_def ("<>") where
  "null_def \<equiv> \<lambda>x. c#0"
syntax 
  "_Defs" :: "updbinds => 'a" ("<_>")
translations
  "_Defs ms" == "_Update <> ms"
  "_Defs (_updbinds b bs)" <= "_Update (_Defs b) bs"
declare null_def_def[simp]

locale timing =
  fixes pApp :: pApp
begin

inductive eval :: "env \<Rightarrow> defs \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> bool" ("(_/ \<turnstile>_/ _/ \<rightarrow> _)") where
Id:   "\<rho> \<turnstile>\<phi> #i \<rightarrow> (\<rho> ! i)" |
C:    "\<rho> \<turnstile>\<phi> c#v \<rightarrow> v" |
F:    "length es = length vs \<Longrightarrow> (\<And>i. i < length vs \<Longrightarrow> \<rho> \<turnstile>\<phi> (es ! i) \<rightarrow> (vs ! i)) \<Longrightarrow> \<phi> f = fe \<Longrightarrow> vs \<turnstile>\<phi> fe \<rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<phi> ($f: es) \<rightarrow> v" |
P:    "length es = length vs \<Longrightarrow> (\<And>i. i < length es \<Longrightarrow> \<rho> \<turnstile>\<phi> (es ! i) \<rightarrow> (vs ! i)) \<Longrightarrow> pApp p vs = v \<Longrightarrow> \<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow> v" |
If1:  "\<rho> \<turnstile>\<phi> c \<rightarrow> v \<Longrightarrow> true v \<Longrightarrow> \<rho> \<turnstile>\<phi> t \<rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF c THEN t ELSE f) \<rightarrow> v" |
If2:  "\<rho> \<turnstile>\<phi> c \<rightarrow> v \<Longrightarrow> false v \<Longrightarrow> \<rho> \<turnstile>\<phi> f \<rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<phi> (IF c THEN t ELSE f) \<rightarrow> v"

inductive_cases IdE[elim!]: "\<rho> \<turnstile>\<phi> #i \<rightarrow> v"
inductive_cases CE[elim!]: "\<rho> \<turnstile>\<phi> c#v' \<rightarrow> v"
inductive_cases FE[elim!]: "\<rho> \<turnstile>\<phi> ($f: es) \<rightarrow> v"
inductive_cases PE[elim!]: "\<rho> \<turnstile>\<phi> (p$p: es) \<rightarrow> v"
inductive_cases IfE[elim!]: "\<rho> \<turnstile>\<phi> (IF c THEN t ELSE f) \<rightarrow> v"

proposition "\<lbrakk> \<rho> \<turnstile>\<phi> e \<rightarrow> v; \<rho> \<turnstile>\<phi> e \<rightarrow> v' \<rbrakk> \<Longrightarrow> v = v'"
proof (induction arbitrary: v' rule: eval.induct)
  case (F es vs \<rho> \<phi> f fe v)
  then show ?case by (metis nth_equalityI FE)
next
  case (P es vs \<rho> \<phi> p v)
  then show ?case by (metis nth_equalityI PE)
qed blast+

end

end
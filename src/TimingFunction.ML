fun get_constrs thy (Type (n, _)) = these (BNF_LFP_Compat.get_constrs thy n)
    | get_constrs _ _ = []
(* returns if something is a constructor (found in smt_normalize.ML) *)
fun is_constr thy (n, T) =
    let fun match (m, U) = m = n andalso Sign.typ_instance thy (T, U)
    in can (the o find_first match o get_constrs thy o Term.body_type) T end

(* Trivial should be everything which is a constructor or something like a constant or variable *)
(* TODO find better way to detect constants *)
val customTrivials = ["Groups.plus_class.plus", "Num.numeral_class.numeral"]
fun is_trivial ctxt (n, (T as Type (Tn,_))) = (Tn <> "fun" orelse is_constr ctxt (n, T) orelse exists (fn c => c = n) customTrivials)
  | is_trivial _ _  = false
(* single terms are always assumed as trivial, only concatenated could be not trivial *)
fun is_trivial_fun ctxt (Const T $ _) = (is_trivial ctxt T)
  | is_trivial_fun ctxt (Free T $ _) = (is_trivial ctxt T)
  | is_trivial_fun ctxt (t $ _) = is_trivial_fun ctxt t
  | is_trivial_fun _ _ = true

(* some default values to build terms easier *)
val natTyp = Type ("Nat.nat", [])
val zero = Const ("Groups.zero_class.zero", natTyp)
val one = Const ("Groups.one_class.one", natTyp);

(* change type of the equality term from _ \<Rightarrow> _ \<Rightarrow> bool to nat \<Rightarrow> nat \<Rightarrow> bool *)
fun change_eq_typ' (TFree _) = natTyp
  | change_eq_typ' t = t
fun change_eq_typ (t as Type (n, [T1, T2])) = (if n = "fun" then Type (n, [change_eq_typ' T1, change_eq_typ T2]) else t)
  | change_eq_typ t = t;

(* change type of original function to new type (_ \<Rightarrow> ... \<Rightarrow> _ to _ \<Rightarrow> ... \<Rightarrow> nat) *)
fun change_typ (t as Type (n, [T1, T2])) = (if n = "fun" then Type (n, [T1, change_typ T2]) else t)
  | change_typ (TVar _) = natTyp
  | change_typ t = t

(* helper function to add two natural, optional terms *)
val plusTyp = Type ("fun", [natTyp, Type ("fun", [natTyp, natTyp])])
fun plus (SOME a) (SOME b) = SOME (Const ("Groups.plus_class.plus", plusTyp) $ a $ b)
  | plus (SOME a) NONE = SOME a
  | plus NONE (SOME b) = SOME b
  | plus NONE NONE = NONE

(* Currently does basically nothing. Should later replace functions by their running time equivalent
    which are not the orignal function (which has already been replaced) *)
fun replace_fun ctxt (t1 $ t2) = (case replace_fun ctxt t1 of SOME t => SOME (t $ t2) | _ => NONE)
  | replace_fun _ (Const (n, T)) = SOME (Const (n, change_typ T))
  | replace_fun _ (Free (n, T)) = SOME (Free (n, change_typ T))
  | replace_fun _ _ = NONE

(* traverses through the term and keeps nontrivial elements *)
fun to_time' ctxt (t as _ $ _) = (if is_trivial_fun ctxt t then NONE else replace_fun ctxt t)
  | to_time' _ _ = NONE
(* Converts the right side of an equation to it's running time function equivalent, current state:
    - Converts highest layer if its timing function if nontrivial, ignores if trivial
    TODO:
    - also add all the arguments of the top level function
*)
fun to_time ctxt t = (case plus (SOME one) (to_time' ctxt t) of SOME t => t | _ => t)

fun separate sep prts =
  flat (Library.separate [Pretty.str sep] (map single prts));

fun terms_of_info (info: Function.info) =
let
  val {simps, ...} = info
in
  map Thm.prop_of (case simps of SOME s => s | NONE => [])
end;

fun print_fun ctxt title (info: Function.info) =
let
  val {defname, fs, ...} = info;
  val name = Binding.name_of defname;
  val typ = (case fs of (Const (_, typ)::_) => typ | (Free (_, typ)::_) => typ | _ => raise Fail "Type of function not implemented")
  val trms = terms_of_info info;
  val header_beg = Pretty.str ("fun " ^ name ^ " :: ");
  val header_end = Pretty.str (" where\n  ");
  val header = [header_beg, Pretty.quote (Syntax.pretty_typ ctxt typ), header_end];
  val ptrms = (separate "\n| " (map (Syntax.pretty_term ctxt) trms));
  val lines = header @ ptrms;
in
  Pretty.writeln (Pretty.text_fold [Pretty.str (title ^ "\n"), Pretty.item lines])
end;

fun register_time_func (lthy: local_theory) (term: term) (info: Function.info) =
  let
    val name = Term.term_name term
    val timing_name = "T_" ^ name
    val (full_name, _) = term |> dest_Const

    val {is_partial, ...} = info
    val bindings = [(Binding.name timing_name, NONE, NoSyn)]
    val fun_config = Function_Common.FunctionConfig
      {sequential=false, default=NONE, domintros=false, partials=is_partial}
    val terms = terms_of_info info;
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt

    (* Variables in simp terms need to be adjusted:
        - Var by their Free equivalent
        - Function itself by its timing function:
          - Change name from "name" to "T_name"
          - Change type from "_ \<Rightarrow> \<dots> \<Rightarrow> _" to "_ \<Rightarrow> \<dots> \<Rightarrow> nat"
    *)
    fun fixTerms (Var(ixn,T)) = Free (fst ixn, T)
      | fixTerms (c as Const(nm,T)) = if member (op=) [full_name] nm then Free (timing_name,change_typ T) else c
      | fixTerms t = t
    (* In types we also need to use the Free equivalent *)
    fun fixTypes (TVar ((t, _), T)) = TFree (t, T)
      | fixTypes t = t
    (* after changing types of variables and types we need to change the actual semantic:
        - Change type of equation from "_ \<Rightarrow> _ \<Rightarrow> bool" to "nat \<Rightarrow> nat \<Rightarrow> bool"
        - Run the to_time function on the right side of the equation to convert it
    *)
    fun parseTerms ((Const pT) $ (Const (eqN, eqT) $ l $ r)) = (Const pT) $ (Const (eqN, change_eq_typ eqT) $ l $ to_time (Proof_Context.theory_of lthy) r)
      | parseTerms _ = raise Fail "Invalid term to convert"
    val timing_terms = (map (map_aterms fixTerms #> map_types (map_atyps fixTypes) #> parseTerms) terms)

    val specs = map (fn eq => (((Binding.empty, []), eq), [], [])) timing_terms
    val (_, lthy') =
      Function.add_function bindings specs fun_config pat_completeness_auto lthy
    val (info, lthy'') =
      Function.prove_termination NONE (Lexicographic_Order.lexicographic_order_tac false lthy') lthy'
  in
    (info, lthy'')
  end;

fun convert func (lthy: local_theory) =
let
val fterm = Syntax.read_term lthy func
val info = Function.get_info lthy fterm
val (time_info, lthy') = register_time_func lthy fterm info
val print_ctxt = Config.put show_question_marks false lthy'
in (print_fun print_ctxt "Original function:" info; print_fun print_ctxt "Timing function:" time_info; lthy')
end;

(* TODO can't deal with non automatic termination *)
Outer_Syntax.local_theory @{command_keyword "define_time_fun"}
"Defines runtime function of a function"
  (Parse.prop >> (fn func => convert func));

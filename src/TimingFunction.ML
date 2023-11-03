
signature TIMING_FUNCTIONS =
sig

val fun_pretty:  Proof.context -> Function.info -> Pretty.T
val print_timing:  Proof.context -> Function.info -> Function.info -> bool -> unit
val reg_time_func: local_theory -> term -> bool -> bool -> Function.info * local_theory
val reg_time_func_cmd: string -> bool -> local_theory -> local_theory

end

structure Timing_Functions : TIMING_FUNCTIONS =
struct

fun get_constrs thy (Type (n, _)) = these (BNF_LFP_Compat.get_constrs thy n)
  | get_constrs _ _ = []
(* returns if something is a constructor (found in smt_normalize.ML) *)
fun is_constr thy (n, T) =
    let fun match (m, U) = m = n andalso Sign.typ_instance thy (T, U)
    in can (the o find_first match o get_constrs thy o Term.body_type) T end

datatype timing_term =
  CONST
| TERM of term
| PLUS of (timing_term * timing_term)
| IF of (term * timing_term * timing_term)
| FUN of (term * term list)

(* Trivial should be everything which is a constructor or something like a constant or variable *)
(* TODO find better way to detect constants *)
fun is_trivial ctxt (n, (T as Type (Tn,_))) = (Tn <> "fun" orelse is_constr ctxt (n, T) orelse is_trivial_decl ctxt n)
  | is_trivial _ _  = false
(* single terms are always assumed as trivial, only concatenated could be not trivial *)
fun is_trivial_fun ctxt (Const T $ _) = (is_trivial ctxt T)
  | is_trivial_fun ctxt (Free T $ _) = (is_trivial ctxt T)
  | is_trivial_fun ctxt (t $ _) = is_trivial_fun ctxt t
  | is_trivial_fun _ _ = true
(* returns true if it's an if term *)
fun is_if (t $ _) = is_if t
  | is_if (Const (n,_)) = (n = "HOL.If")
  | is_if _ = false

(* some default values to build terms easier *)
val natTyp = Type ("Nat.nat", [])
val zero = Const ("Groups.zero_class.zero", natTyp)
val one = Const ("Groups.one_class.one", natTyp);

(* helper function to add two natural, optional terms - normal and asymptotic version *)
val plusTyp = Type ("fun", [natTyp, Type ("fun", [natTyp, natTyp])])
fun plus (SOME a) (SOME b) = SOME (Const ("Groups.plus_class.plus", plusTyp) $ a $ b)
  | plus (SOME a) NONE = SOME (Const ("Groups.plus_class.plus", plusTyp) $ a $ one)
  | plus NONE (SOME b) = SOME (Const ("Groups.plus_class.plus", plusTyp) $ one $ b)
  | plus NONE NONE = SOME (Const ("Groups.plus_class.plus", plusTyp) $ one $ one)
fun aplus (SOME a) (SOME b) = SOME (Const ("Groups.plus_class.plus", plusTyp) $ a $ b)
  | aplus (SOME a) NONE = SOME a
  | aplus NONE (SOME b) = SOME b
  | aplus NONE NONE = NONE
fun opt_term NONE = one
  | opt_term (SOME t) = t
fun aopt_term NONE = zero
  | aopt_term (SOME t) = t
fun timing_term_term (TERM t) = t
  | timing_term_term _ = raise ERROR "Cannot change non TERM to term"
(* Compose an if term - normal and asymptotic version *)
fun if_term cond t f =
  SOME ((Const ("HOL.If", @{typ "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"})) $ cond $ (opt_term t) $ (opt_term f))
(* Compose an if term if the true and false terms are not NONE *)
fun aif_term _ NONE NONE = NONE
  | aif_term cond t f =
  SOME ((Const ("HOL.If", @{typ "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"})) $ cond $ (aopt_term t) $ (aopt_term f));

(* change type of the equality term from _ \<Rightarrow> _ \<Rightarrow> bool to nat \<Rightarrow> nat \<Rightarrow> bool *)
fun change_eq_typ (t as Type (n, [_, T2])) = (if n = "fun" then Type (n, [natTyp, change_eq_typ T2]) else t)
  | change_eq_typ t = t;

(* change type of original function to new type (_ \<Rightarrow> ... \<Rightarrow> _ to _ \<Rightarrow> ... \<Rightarrow> nat) *)
fun change_typ (t as Type (n, [T1, T2])) = (if n = "fun" then Type (n, [T1, change_typ T2]) else t)
  | change_typ _ = natTyp

(* Convert string name of function to its timing equivalent *)
fun fun_name_to_time name =
let
  fun replace_last_name [n] = ["T_" ^ n]
    | replace_last_name (n::ns) = n :: (replace_last_name ns)
    | replace_last_name _ = raise ERROR "Invalid function with empty name"
  val parts = String.fields (fn s => s = #".") name
in
  String.concatWith "." (replace_last_name parts)
end
(* Check if it's the same theory *)
fun same_theory t1 t2 =
let
  val splitter = (fn s => s = #".")
  val parts1 = String.fields splitter t1
  val parts2 = String.fields splitter t2
in
  (take (length parts1 - 1) parts1) = (take (length parts2 - 1) parts2)
end

(* Convert the function name to it's time function and change typ *)
fun fun_to_time ctxt orig (c as Const(nm,T)) =
let
  val name = Term.term_name orig
  val timing_name_orig = "T_" ^ name
  val (full_name, _) = orig |> dest_Const
in
  if nm = full_name then TERM (Free (timing_name_orig, change_typ T)) else
  if not (same_theory full_name nm) then raise ERROR "Can only convert functions of this theory" else
  let
    val timing_name_other = fun_name_to_time nm
  in
    (* TODO find better way to detect if timing function is already defined *)
    (Syntax.read_term_global ctxt timing_name_other |> TERM)
          handle _ => FUN (c, [])
  end
end
| fun_to_time _ _ _ = raise ERROR "Invalid type cannot ne exchanged to time"

(* Traverses fun term and calls fun_to_time on the first Const element *)
fun create_fun (TERM t1) t2 = TERM (t1 $ t2)
  | create_fun (FUN (f, ts)) t = FUN (f, ts@[t])
  | create_fun _ _ = raise ERROR "Invalid type to build FUN"
fun replace_fun ctxt orig ((c as Const _) $ t2) = create_fun (fun_to_time ctxt orig c) t2
  | replace_fun ctxt orig (t1 $ t2) = create_fun (replace_fun ctxt orig t1) t2
  | replace_fun _ _ _ = raise ERROR "No valid term to replace fun"

(* traverses through the term and keeps nontrivial elements *)
fun to_time' ctxt orig (t as _ $ _) =
  (if is_if t then to_time_if ctxt orig t else  
    PLUS (if is_trivial_fun ctxt t then CONST else replace_fun ctxt orig t, to_time_el ctxt orig t))
  | to_time' _ _ _ = CONST
(* processes the arguments of a function *)
and to_time_el ctxt orig ((t1 as (_ $ _)) $ t2) = PLUS (to_time_el ctxt orig t1, to_time' ctxt orig t2)
  | to_time_el ctxt orig (_ $ t2) = to_time' ctxt orig t2
  | to_time_el _ _ _ = CONST
(* processes an if term *)
and to_time_if ctxt orig (_ $ cond $ t $ f) = PLUS (IF (cond, to_time' ctxt orig t, to_time' ctxt orig f), to_time' ctxt orig cond)
  | to_time_if _ _ _ = raise ERROR "Invalid if term"

fun separate sep prts =
  flat (Library.separate [Pretty.str sep] (map single prts));

fun terms_of_info (info: Function.info) =
let
  val {simps, ...} = info
in
  map Thm.prop_of (case simps of SOME s => s | NONE => [])
end;

fun fun_pretty ctxt (info: Function.info) =
let
  val {defname, fs, ...} = info;
  val name = Binding.name_of defname;
  val typ = (case fs of (Const (_, typ)::_) => typ | (Free (_, typ)::_) => typ | _ => raise ERROR "Type of function not implemented")
  val trms = terms_of_info info;
  val header_beg = Pretty.str ("fun " ^ name ^ " :: ");
  val header_end = Pretty.str (" where\n  ");
  val header = [header_beg, Pretty.quote (Syntax.pretty_typ ctxt typ), header_end];
  val ptrms = (separate "\n| " (map (Syntax.pretty_term ctxt) trms));
in
  Pretty.text_fold (header @ ptrms)
end;

fun print_timing ctxt (oinfo: Function.info) (tinfo: Function.info) asymp =
let
  val {defname, ...} = oinfo;
  val name = Binding.name_of defname;
  val poriginal = Pretty.item [Pretty.str "Original function:\n", fun_pretty ctxt oinfo]
  val ptiming = Pretty.item [Pretty.str ((if asymp then "Asymptotic r" else "R") ^ "unning time function:\n"), fun_pretty ctxt tinfo]
in
  Pretty.writeln (Pretty.text_fold [Pretty.str ("Converting " ^ name ^ "...\n"), poriginal, Pretty.str "\n", ptiming])
end

fun reg_time_func (lthy: local_theory) (term: term) asymp print =
  let
    (* builds term from timing_term *)
    fun build ctxt CONST = (ctxt, SOME one)
      | build ctxt (TERM term) = (ctxt, SOME term)
      | build ctxt (PLUS (t1, t2)) =
      let
        val (ctxt', t1') = build ctxt t1
        val (ctxt'', t2') = build ctxt' t2
      in
        (ctxt'', plus t1' t2')
      end
      | build ctxt (IF (cond, t, f)) =
      let
        val (ctxt', t') = build ctxt t
        val (ctxt'', f') = build ctxt' f
      in
        (ctxt'', if_term cond t' f')
      end
      | build ctxt (FUN (f, args)) =
      let
        val (_, ctxt') = reg_time_func ctxt f false true
        val name = (case f of Const (n,_) => n | _ => raise ERROR "Invalid term")
        val time_name  = fun_name_to_time name
        val time_term = Syntax.parse_term ctxt' time_name
        fun build_fun [] t = t
          | build_fun (a::args) t = build_fun args (t $ a)
      in (ctxt', SOME (build_fun args time_term)) end
    fun abuild ctxt CONST = (ctxt, NONE)
      | abuild ctxt (TERM term) = (ctxt, SOME term)
      | abuild ctxt (PLUS (t1, t2)) =
      let
        val (ctxt', t1') = abuild ctxt t1
        val (ctxt'', t2') = abuild ctxt' t2
      in
        (ctxt'', aplus t1' t2')
      end
      | abuild ctxt (IF (cond, t, f)) =
      let
        val (ctxt', t') = abuild ctxt t
        val (ctxt'', f') = abuild ctxt' f
      in
        (ctxt'', aif_term cond t' f')
      end
      | abuild ctxt (FUN (f, args)) =
      let
        val (_, ctxt') = reg_time_func ctxt f true true
        val name = (case f of Const (n,_) => n | _ => raise ERROR "Invalid term")
        val time_name  = fun_name_to_time name
        val time_term = Syntax.parse_term ctxt' time_name
        fun build_fun [] t = t
          | build_fun (a::args) t = build_fun args (t $ a)
      in (ctxt', SOME (build_fun args time_term)) end
    (* Converts the right side of an equation to it's running time function equivalent, current state:
        - Converts constants
        - Converts own function by replacing with timing equivalent and adding timing equivalent of arguments
        - Ignores trivial terms
        - Converts if terms
        - Converts other functions to their timing equivalent if they are in the same theory
    *)
    fun to_time ctxt orig asymp t = ((if asymp then abuild else build) ctxt (PLUS (TERM one, to_time' (Proof_Context.theory_of ctxt) orig t))) ||> opt_term 

    val info = (Function.get_info lthy term) handle Empty => raise ERROR "Cannot find function in current theory"
    val name = Term.term_name term
    val timing_name = "T_" ^ name
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
      | fixTerms t = t
    (* In types we also need to use the Free equivalent *)
    fun fixTypes (TVar ((t, _), T)) = TFree (t, T)
      | fixTypes t = t
    (* after changing types of variables and types we need to change the actual semantic:
        - Change type of equation from "_ \<Rightarrow> _ \<Rightarrow> bool" to "nat \<Rightarrow> nat \<Rightarrow> bool"
        - Run the to_time function on the right side of the equation to convert it
    *)
    fun convertTerm ctxt ((Const pT) $ (Const (eqN, eqT) $ l $ r)) =
      let val (ctxt, r') = to_time ctxt term asymp r
      in (ctxt, (Const pT) $ (Const (eqN, change_eq_typ eqT) $ timing_term_term (replace_fun (Proof_Context.theory_of lthy) term l) $ r')) end
      | convertTerm _ _ = raise ERROR "Invalid term to convert"
    fun convertTerms ctxt [] = (ctxt, [])
      | convertTerms ctxt (t::ts) =
      let
        val (ctxt', t') = convertTerm ctxt (map_aterms fixTerms t |> map_types (map_atyps fixTypes))
        val (ctxt'', ts') = convertTerms ctxt' ts
      in (ctxt'', t'::ts') end
    val (lthy', timing_terms) = convertTerms lthy terms

    val specs = map (fn eq => (((Binding.empty, []), eq), [], [])) timing_terms
    val (_, lthy'') =
      Function.add_function bindings specs fun_config pat_completeness_auto lthy'
    val (time_info, lthy''') =
      Function.prove_termination NONE (Lexicographic_Order.lexicographic_order_tac false lthy'') lthy''
    
    val print_ctxt = Config.put show_question_marks false lthy'
    val _ = (if print then print_timing print_ctxt info time_info asymp else ())
  in
    (time_info, lthy''')
  end;

fun reg_time_func_cmd func asymp (lthy: local_theory) =
let
val fterm = Syntax.read_term lthy func
val (_, lthy') = reg_time_func lthy fterm asymp true
in lthy'
end;

(* TODO can't deal with non automatic termination *)
val _ = Outer_Syntax.local_theory @{command_keyword "define_time_fun"}
"Defines runtime function of a function"
  (Parse.prop >> (fn func => reg_time_func_cmd func false));
(* TODO can't deal with non automatic termination *)
val _ = Outer_Syntax.local_theory @{command_keyword "define_atime_fun"}
"Defines runtime function of a function"
  (Parse.prop >> (fn func => reg_time_func_cmd func true));

end

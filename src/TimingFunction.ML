
signature TIMING_FUNCTIONS =
sig

val fun_pretty:  Proof.context -> Function.info -> Pretty.T
val print_timing:  Proof.context -> Function.info -> Function.info -> bool -> unit
val reg_time_func: local_theory -> term -> bool -> bool -> Function.info * local_theory
val reg_time_func_cmd: string -> bool -> local_theory -> local_theory

val time_dom_tac: Proof.context -> thm -> thm list -> int -> tactic

type 'a converter = {
  constc : local_theory -> term -> (term -> 'a) -> term -> 'a,
  funcc : local_theory -> term -> (term -> 'a) -> term -> term list -> 'a,
  ifc : local_theory -> term -> (term -> 'a) -> term -> term -> term -> 'a
};
val walk : local_theory -> term -> 'a converter -> term -> 'a

end

structure Timing_Functions : TIMING_FUNCTIONS =
struct
(* some default values to build terms easier *)
val natTyp = Type ("Nat.nat", [])
val zero = Const ("Groups.zero_class.zero", natTyp)
val one = Const ("Groups.one_class.one", natTyp);
(* Extracts terms from function info *)
fun terms_of_info (info: Function.info) =
let
  val {simps, ...} = info
in
  map Thm.prop_of (case simps of SOME s => s | NONE => raise ERROR "Function has no terms")
end;

(* Auxiliary functions for printing functions *)
fun fun_pretty ctxt (info: Function.info) =
let
  val {defname, fs, ...} = info;
  val name = Binding.name_of defname;
  val typ = (case fs of (Const (_, typ)::_) => typ | (Free (_, typ)::_) => typ | _ => raise ERROR "Type of function not implemented")
  val trms = terms_of_info info;
  val header_beg = Pretty.str ("fun " ^ name ^ " :: ");
  val header_end = Pretty.str (" where\n  ");
  val header = [header_beg, Pretty.quote (Syntax.pretty_typ ctxt typ), header_end];
  fun separate sep prts =
    flat (Library.separate [Pretty.str sep] (map single prts));
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
end;

(* returns true if it's an if term *)
fun is_if (Const (n,_)) = (n = "HOL.If")
  | is_if _ = false
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

type 'a converter = {
  constc : local_theory -> term -> (term -> 'a) -> term -> 'a,
  funcc : local_theory -> term -> (term -> 'a) -> term -> term list -> 'a,
  ifc : local_theory -> term -> (term -> 'a) -> term -> term -> term -> 'a
};

(* Walks over term and calls given converter *)
fun walk_func (t1 $ t2) ts = walk_func t1 (t2::ts)
  | walk_func t ts = (t, ts)
fun build_func (f, []) = f
  | build_func (f, (t::ts)) = build_func (f$t, ts)
fun walk ctxt origin (conv as {ifc, funcc, ...}) (t as _ $ _) =
  let
    val (f, args) = walk_func t []
    val this = (walk ctxt origin conv)
  in
    (if is_if f then
      (case args of [cond, t, f] => ifc ctxt origin this cond t f
                  | _ => raise ERROR "Invalid if term")
      else funcc ctxt origin this f args)
  end
  | walk ctxt origin (conv as {constc, ...}) c = 
    constc ctxt origin (walk ctxt origin conv) c

(* 1. Fix all terms *)
(* Exchange Var in types and terms to Free *)
fun fixTerms (Var(ixn,T)) = Free (fst ixn, T)
  | fixTerms t = t
fun fixTypes (TVar ((t, _), T)) = TFree (t, T)
  | fixTypes t = t

(* 2. Check for undefined timing functions *)
fun right_of_equation (_ $ (_ $ _ $ r)) = r
  | right_of_equation _ = raise ERROR "Invalid equation"
(* Check if it's the same theory *)
fun same_theory t1 t2 =
let
  val splitter = (fn s => s = #".")
  val parts1 = String.fields splitter t1
  val parts2 = String.fields splitter t2
in
  (take (length parts1 - 1) parts1) = (take (length parts2 - 1) parts2)
end
(* Returns list of all function without a defined timing function *)
fun check_fun ctxt origin f (func as Const (nm,T)) args =
let
  val name_origin = origin |> dest_Const |> fst
  val f_args = List.foldr (List.@) [] (map f args)
in
  if nm = name_origin orelse Trivial_Funcs.is_trivial (Proof_Context.theory_of ctxt) (nm,T) then [] else
  if not (same_theory name_origin nm) then raise ERROR ("Can only convert functions of this theory"^nm) else
  (Syntax.check_term ctxt (Const (fun_name_to_time nm, change_typ T)) |> (K f_args))
        handle (ERROR _) => func :: f_args
end
  | check_fun _ _ _ _ _ = raise ERROR "Invalid function"
(* Returns list of all functions with undefined timing functions *)
fun find_missing ctxt term terms = 
  List.foldr (List.@) []
    (map (walk ctxt term {
        funcc = check_fun,
        constc = ((K o K o K o K) []),
        ifc = (fn _ => fn _ => fn f => fn _ => fn t => fn r => f t @ f r)
    }) terms)

(* 3. Convert equations *)
(* Change every term *)
fun fun_to_time ctxt origin (Const (nm,T)) =
let
  val timing_name_origin = "T_" ^ Term.term_name origin
  val full_name_origin = origin |> dest_Const |> fst
  val timing_name_other = fun_name_to_time nm
in
  if nm = full_name_origin then SOME (Free (timing_name_origin, change_typ T)) else
  if Trivial_Funcs.is_trivial (Proof_Context.theory_of ctxt) (nm,T) then NONE else
  SOME (Const (timing_name_other, change_typ T))
end
  | fun_to_time _ _ _ = raise ERROR "Invalid function to convert"

(* Normal conversion *)
val plusTyp = @{typ "nat => nat => nat"}
fun plus a b = (Const ("Groups.plus_class.plus", plusTyp) $ a $ b)
fun opt_term NONE = one
  | opt_term (SOME t) = t
fun funcc ctxt origin f func args = List.foldr (I #-> plus)
  (case fun_to_time ctxt origin func of SOME t => build_func (t,args) | NONE => one) (map f args)
fun ifc _ _ f cond tt ft =
  plus ((Const ("HOL.If", @{typ "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"})) $ cond $ (f tt) $ (f ft)) (f cond)
fun to_time ctxt origin term =
  plus one (walk ctxt origin {
        constc = fn _ => fn _ => fn _ => fn _ => one,
        funcc = funcc,
        ifc = ifc
    } term)
(* Asymptotic conversion *)
fun aplus (SOME a) (SOME b) = SOME (Const ("Groups.plus_class.plus", plusTyp) $ a $ b)
  | aplus (SOME a) NONE = SOME a
  | aplus NONE (SOME b) = SOME b
  | aplus NONE NONE = NONE
fun aopt_term NONE = zero
  | aopt_term (SOME t) = t
(* Compose an if term if the true and false terms are not NONE *)
fun afuncc ctxt origin f func args = List.foldr (I #-> aplus) 
  (case fun_to_time ctxt origin func of SOME t => SOME (build_func (t,args)) | NONE => NONE) (map f args)
fun aifc _ _ f cond tt ft =
  let
    val tt = f tt
    val ft = f ft
  in
    (case (tt,ft) of (NONE, NONE) => NONE | _=>    
      aplus (SOME ((Const ("HOL.If", @{typ "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"})) $ cond $ (aopt_term tt) $ (aopt_term ft))) (f cond))
  end
fun to_time_asymp ctxt origin term = 
  (opt_term o (aplus (SOME one))) (walk ctxt origin {
        constc = fn _ => fn _ => fn _ => fn _ => NONE,
        funcc = afuncc,
        ifc = aifc
    } term)

(* Converts a term to its running time version *)
fun convert_term ctxt origin asymp (pT $ (Const (eqN, _) $ l $ r)) =
      pT
      $ (Const (eqN, @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"})
        $ (build_func ((walk_func l []) |>> (fun_to_time ctxt origin) |>> Option.valOf))
        $ (((if asymp then to_time_asymp else to_time) ctxt origin) r))
  | convert_term _ _ _ _ = raise ERROR "Invalid term to convert"

(* Tactic to prove "f_dom n" *)
fun time_dom_tac ctxt induct_rule domintros =
  Induction.induction_tac ctxt true [] [[]] [] (SOME [induct_rule]) []
      THEN_ALL_NEW (Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt domintros)

(* Convert given function into a timing function *)
fun reg_time_func (lthy: local_theory) (term: term) asymp print =
  let
    val info = (Function.get_info lthy term) handle Empty => raise ERROR "Cannot find function in current theory"
    val terms = terms_of_info info;

    (* 1. Fix all terms *)
    (* Exchange Var in types and terms to Free *)
    val terms = map (map_aterms fixTerms #> map_types (map_atyps fixTypes)) terms

    (* 2. Find missing functions and define them *)
    val missing_funcs = find_missing lthy term (map right_of_equation terms)
    val lthy = List.foldr (fn (f, ctxt) => reg_time_func ctxt f asymp print |> snd) lthy missing_funcs
    
    (* 3. Convert every equation
      - Change type of toplevel equation from _ \<Rightarrow> _ \<Rightarrow> bool to nat \<Rightarrow> nat \<Rightarrow> bool
      - On left side change name of function to timing function
      - Convert right side of equation with conversion schema
    *)
    val timing_terms' = map (convert_term lthy term asymp) terms

    (* 4. Register function and prove termination *)
    val name = Term.term_name term
    val timing_name = "T_" ^ name
    val {is_partial, ...} = info
    val bindings = [(Binding.name timing_name, NONE, NoSyn)]
    val fun_config = Function_Common.FunctionConfig
      {sequential=false, default=NONE, domintros=true, partials=is_partial}
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
    val specs = map (fn eq => (((Binding.empty, []), eq), [], [])) timing_terms'
    
    (* Register function *)
    val (_, lthy) =
      Function.add_function bindings specs fun_config pat_completeness_auto lthy

    (* Start proving the termination *)
    fun args (a$_) = args a |> (fn (x,ar) => (x^"x",x::ar))
      | args _ = ("x",[])
    val dom_args = (case terms of ((_ $ (_ $ l $ _))::_) => args l |> snd | _ => raise ERROR "Invalid function")
    
    val {inducts, ...} = info
    val induct = (Option.valOf inducts |> hd)               
    val lthy' = Named_Target.theory_init (Proof_Context.theory_of lthy)
  
    val domintros = Proof_Context.get_fact lthy' (Facts.named (timing_name ^ ".domintros"))

    val prop = (timing_name ^ "_dom (" ^ (String.concatWith "," dom_args) ^ ")")
                |> Syntax.read_prop lthy'
    (* Prove a helper lemma *)
    val dom_lemma = Goal.prove lthy' dom_args [] prop
      (fn {context, ...} => HEADGOAL (time_dom_tac context induct domintros))
    (* Add dom_lemma to simplification set *)
    val simp_lthy = Simplifier.add_simp dom_lemma lthy'

    (* Use lemma to prove termination *)
    val (time_info, lthy'') =
      Function.prove_termination NONE (auto_tac simp_lthy) lthy'
    
    (* Context for printing without showing question marks *)
    val print_ctxt = Config.put show_question_marks false lthy''
    (* Print result if print *)
    val _ = (if print then print_timing print_ctxt info time_info asymp else ())
  in
    (time_info, lthy'')
  end;

(* Convert function into its timing function (called by command) *)
fun reg_time_func_cmd func asymp (lthy: local_theory) =
let
  val fterm = Syntax.read_term lthy func
  val (_, lthy') = reg_time_func lthy fterm asymp true
in lthy'
end;

val _ = Outer_Syntax.local_theory @{command_keyword "define_time_fun"}
  "Defines runtime function of a function"
  (Parse.prop >> (fn func => reg_time_func_cmd func false));
val _ = Outer_Syntax.local_theory @{command_keyword "define_atime_fun"}
  "Defines runtime function of a function"
  (Parse.prop >> (fn func => reg_time_func_cmd func true));

end

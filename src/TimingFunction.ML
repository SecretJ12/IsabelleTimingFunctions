
signature TIMING_FUNCTIONS =
sig

val fun_pretty:  Proof.context -> Function.info -> Pretty.T
val print_timing:  Proof.context -> Function.info -> Function.info -> bool -> unit
val reg_time_func: theory -> term -> bool -> bool -> Function.info * theory
val reg_time_func_cmd: string -> bool -> theory -> theory

val time_dom_tac: Proof.context -> thm -> thm list -> int -> tactic

type 'a converter = {
  constc : local_theory -> term -> (term -> 'a) -> term -> 'a,
  funcc : local_theory -> term -> (term -> 'a) -> term -> term list -> 'a,
  ifc : local_theory -> term -> (term -> 'a) -> term -> term -> term -> 'a,
  casec : local_theory -> term -> (term -> 'a) -> term -> term list -> 'a
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
(* returns true if it's an case term *)
fun is_case (Const (n,_)) = String.isPrefix "case_" (List.last (String.fields (fn s => s = #".") n))
  | is_case _ = false
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
  ifc : local_theory -> term -> (term -> 'a) -> term -> term -> term -> 'a,
  casec : local_theory -> term -> (term -> 'a) -> term -> term list -> 'a
};

(* Walks over term and calls given converter *)
fun walk_func (t1 $ t2) ts = walk_func t1 (t2::ts)
  | walk_func t ts = (t, ts)
fun build_func (f, []) = f
  | build_func (f, (t::ts)) = build_func (f$t, ts)
fun walk ctxt origin (conv as {ifc, casec, funcc, ...}) (t as _ $ _) =
  let
    val (f, args) = walk_func t []
    val this = (walk ctxt origin conv)
  in
    (if is_if f then
      (case args of [cond, t, f] => ifc ctxt origin this cond t f
                  | _ => raise ERROR "Invalid if term")
      else if is_case f then casec ctxt origin this f args
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
val _ = Variable.variant_fixes
fun casecBuildBounds n t = if n > 0 then casecBuildBounds (n-1) (t $ (Bound (n-1))) else t
fun casecAbs ctxt f n (Type (_,[_,Tr])) (Abs (v,Ta,t)) = Abs (v,Ta,casecAbs ctxt f n Tr t)
  | casecAbs ctxt f n (Type (Tn,[T,Tr])) t =
    (case Variable.variant_fixes ["x"] ctxt of ([v],ctxt) =>
    (if Tn = "fun" then Abs(v,T,casecAbs ctxt f (n + 1) Tr t) else f t)
    | _ => raise ERROR "Could not fix variables")
  | casecAbs _ f n _ t = f (casecBuildBounds n t)
fun fixCasecCases _ _ _ [t] = [t]
  | fixCasecCases ctxt f (Type (_,[T,Tr])) (t::ts) = casecAbs ctxt f 0 T t :: fixCasecCases ctxt f Tr ts
  | fixCasecCases _ _ _ _ = raise ERROR "Invalid case types/terms"
fun fixCasec ctxt _ f (t as Const (_,T)) args = build_func (t,fixCasecCases ctxt f T args)
  | fixCasec _ _ _ _ _ = raise ERROR "Invalid case term"
fun fixPartTerms ctxt term (pT $ (eq $ l $ r)) =
  pT $ (eq $ l $ (walk ctxt term {
        funcc = (fn _ => fn _ => fn f => fn t => fn args => build_func (t, map f args)),
        constc = (fn _ => fn _ => fn _ => fn c => c),
        ifc = (fn _ => fn _ => fn f => fn cond => fn tt => fn tf =>
          ((Const ("HOL.If", @{typ "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"})) $ f cond $ (f tt) $ (f tf))),
        casec = fixCasec
    } r))
  | fixPartTerms _ _ _ = raise ERROR "Invalid term to fix"

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
  (Syntax.check_term ctxt (Const (fun_name_to_time nm, change_typ T)) |> (K f_args))
        handle (ERROR _) =>
  if not (same_theory name_origin nm) then raise ERROR ("Can only convert functions of this theory: "^nm)
    else func :: f_args
end
  | check_fun _ _ _ _ _ = raise ERROR "Invalid function"
(* Returns list of all functions with undefined timing functions *)
fun casecMisAbs f (Abs (_,_,t)) = casecMisAbs f t
  | casecMisAbs f t = f t
fun find_missing ctxt term terms =
  List.foldr (List.@) []
    (map (walk ctxt term {
        funcc = check_fun,
        constc = ((K o K o K o K) []),
        ifc = (fn _ => fn _ => fn f => fn cond => fn t => fn r => f cond @ f t @ f r),
        casec = (fn _ => fn _ => fn f => fn t => fn args => f t @ List.foldr (fn (t,fs) => casecMisAbs f t @ fs) [] args)
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
fun casecAbs f (Abs (v,Ta,t)) = Abs (v,Ta,casecAbs f t)
  | casecAbs f t = f t
fun casecArgs _ [t] = [t]
  | casecArgs f (t::ar) = casecAbs f t :: casecArgs f ar
  | casecArgs _ _ = raise ERROR "Invalid case term"
fun casecIsCase (Type (n1, [_,Type (n2, _)])) = (n1 = "fun" andalso n2 = "fun")
  | casecIsCase _ = false
fun casecLastTyp (Type (n, [T1,T2])) = Type (n, [T1, change_typ T2])
  | casecLastTyp _ = raise ERROR "Invalid case type"
fun casecTyp (Type (n, [T1, T2])) =
      Type (n, [change_typ T1, (if casecIsCase T2 then casecTyp else casecLastTyp) T2])
  | casecTyp _ = raise ERROR "Invalid case type"
fun casec _ _ f (Const (t,T)) args =
  if not (casecIsCase T) then raise ERROR "Invalid case type" else
    plus (build_func (Const (t,casecTyp T), casecArgs f args)) (f (List.last args))
  | casec _ _ _ _ _ = raise ERROR "Invalid case term"
fun to_time ctxt origin term =
  plus one (walk ctxt origin {
        constc = fn _ => fn _ => fn _ => fn _ => one,
        funcc = funcc,
        ifc = ifc,
        casec = casec
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
    (case (tt,ft) of (NONE, NONE) => NONE | _ =>    
      aplus (SOME ((Const ("HOL.If", @{typ "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"})) $ cond $ (aopt_term tt) $ (aopt_term ft))) (f cond))
  end
fun acasecArgs _ [t] = (false, [t])
  | acasecArgs f ((Abs (v,T,t))::ar) =
    (case f t of
        NONE => acasecArgs f ar ||> (fn ar => Abs (v,T,zero) :: ar)
      | SOME t => acasecArgs f ar ||> (fn ar => Abs (v,T,t) :: ar) |>> K true)
  | acasecArgs f (t::ar) =
    (case f t of
        NONE => acasecArgs f ar ||> (fn ar => zero :: ar)
      | SOME t => acasecArgs f ar ||> (fn ar => t :: ar) |>> K true)
  | acasecArgs _ _ = raise ERROR "Invalid case term"
fun acasec _ _ f (Const (t,T)) args =
  if not (casecIsCase T) then raise ERROR "Invalid case type" else
    let val (nconst, args') = acasecArgs f args in
      aplus
        (if nconst then
          SOME (build_func (Const (t,casecTyp T), args'))
         else NONE)
        (f (List.last args))
    end
  | acasec _ _ _ _ _ = raise ERROR "Invalid case term"
fun to_time_asymp ctxt origin term = 
  (opt_term o (aplus (SOME one))) (walk ctxt origin {
        constc = fn _ => fn _ => fn _ => fn _ => NONE,
        funcc = afuncc,
        ifc = aifc,
        casec = acasec
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
  (Induction.induction_tac ctxt true [] [[]] [] (SOME [induct_rule]) []
      THEN_ALL_NEW ((K (auto_tac ctxt)) THEN' (fn i => FIRST' (
        (if i <= length domintros then [Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt [List.nth (domintros, i-1)]] else []) @
        [Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt domintros]) i)))

(* Convert given function into a timing function *)
fun reg_time_func (theory: theory) (term: term) asymp print =
  let
    val lthy = Named_Target.theory_init theory

    val info = (Function.get_info lthy term) handle Empty => raise ERROR "Cannot find function in current theory"
    val terms = terms_of_info info;

    (* 1. Fix all terms *)
    (* Exchange Var in types and terms to Free *)
    val terms = map (map_aterms fixTerms #> map_types (map_atyps fixTypes) #> fixPartTerms lthy term) terms

    (* 2. Find missing functions and define them *)
    val missing_funcs = find_missing lthy term (map right_of_equation terms)
    val theory = Local_Theory.exit_global lthy
    val theory = List.foldr (fn (f, ctxt) => reg_time_func ctxt f asymp print |> snd) theory missing_funcs
    val lthy = Named_Target.theory_init theory
    
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
    val lthy' = Named_Target.theory_init (Local_Theory.exit_global lthy)
  
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
    (time_info, Local_Theory.exit_global lthy'')
  end;

(* Convert function into its timing function (called by command) *)
fun reg_time_func_cmd func asymp (theory: theory) =
let
  val fterm = Syntax.read_term (Proof_Context.init_global theory) func
  val (_, theory') = reg_time_func theory fterm asymp true
in theory'
end;

val _ = Outer_Syntax.command @{command_keyword "define_time_fun"}
  "Defines runtime function of a function"
  (Parse.prop >> (fn func => Toplevel.theory (reg_time_func_cmd func false)));
val _ = Outer_Syntax.command @{command_keyword "define_atime_fun"}
  "Defines runtime function of a function"
  (Parse.prop >> (fn func => Toplevel.theory (reg_time_func_cmd func true)));

end

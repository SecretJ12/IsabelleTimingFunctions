
signature TIMING_FUNCTIONS =
sig
type 'a converter = {
  constc : local_theory -> term -> (term -> 'a) -> term -> 'a,
  funcc : local_theory -> term -> (term -> 'a) -> term -> term list -> 'a,
  ifc : local_theory -> term -> (term -> 'a) -> term -> term -> term -> 'a,
  casec : local_theory -> term -> (term -> 'a) -> term -> term list -> 'a
};
val walk : local_theory -> term -> 'a converter -> term -> 'a

type pfunc = { name : string, terms : term list, typ : typ }
val fun_pretty':  Proof.context -> pfunc -> Pretty.T
val fun_pretty:  Proof.context -> Function.info -> Pretty.T
val print_timing':  Proof.context -> pfunc -> pfunc -> unit
val print_timing:  Proof.context -> Function.info -> Function.info -> unit
val reg_time_func: theory -> term -> 'a converter -> (local_theory -> term -> 'a -> term) -> bool -> Function.info * theory
val reg_time_func_cmd: string -> 'a converter -> (local_theory -> term -> 'a -> term) -> theory -> theory

val time_dom_tac: Proof.context -> thm -> thm list -> int -> tactic

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
  map Thm.prop_of (case simps of SOME s => s | NONE => error "Function has no terms")
end;

type pfunc = {
  name : string,
  terms : term list,
  typ : typ
}
fun info_pfunc (info: Function.info): pfunc =
let
  val {defname, fs, ...} = info;
  val T = case hd fs of (Const (_,T)) => T | _ => error "Invalid info"
in
  { name=Binding.name_of defname, terms=terms_of_info info, typ=T }
end

(* Auxiliary functions for printing functions *)
fun fun_pretty' ctxt (pfunc: pfunc) =
let
  val {name, terms, typ} = pfunc;
  val header_beg = Pretty.str ("fun " ^ name ^ " :: ");
  val header_end = Pretty.str (" where\n  ");
  val header = [header_beg, Pretty.quote (Syntax.pretty_typ ctxt typ), header_end];
  fun separate sep prts =
    flat (Library.separate [Pretty.str sep] (map single prts));
  val ptrms = (separate "\n| " (map (Syntax.pretty_term ctxt) terms));
in
  Pretty.text_fold (header @ ptrms)
end
fun fun_pretty ctxt = fun_pretty' ctxt o info_pfunc
fun print_timing' ctxt (opfunc: pfunc) (tpfunc: pfunc) =
let
  val {name, ...} = opfunc;
  val poriginal = Pretty.item [Pretty.str "Original function:\n", fun_pretty' ctxt opfunc]
  val ptiming = Pretty.item [Pretty.str ("Running time function:\n"), fun_pretty' ctxt tpfunc]
in
  Pretty.writeln (Pretty.text_fold [Pretty.str ("Converting " ^ name ^ "...\n"), poriginal, Pretty.str "\n", ptiming])
end
fun print_timing ctxt (oinfo: Function.info) (tinfo: Function.info) =
  print_timing' ctxt (info_pfunc oinfo) (info_pfunc tinfo)

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
    | replace_last_name _ = error "Invalid function with empty name"
  val parts = String.fields (fn s => s = #".") name
in
  String.concatWith "." (replace_last_name parts)
end
(* Count number of arguments of a function *)
fun count_args (Type (n, [_,res])) = (if n = "fun" then 1 + count_args res else 0)
  | count_args _ = 0
(* Check if number of arguments matches function *)
fun check_args s (Const (_,T), args) =
    (if length args = count_args T then () else error ("Partial applications/Lambdas not allowed (" ^ s ^ ")"))
  | check_args s _ = error ("Partial applications/Lambdas not allowed (" ^ s ^ ")")

fun time_term ctxt (Const (nm,T)) =
let
  val T_nm = fun_name_to_time nm
  val T_T = change_typ T
in
(SOME (Syntax.check_term ctxt (Const (T_nm,T_T))))
  handle (ERROR _) =>
    case Syntax.read_term ctxt (Long_Name.base_name T_nm)
      of (t as Const _) => SOME t
       | _ => NONE
end
  | time_term _ _ = error "Invalid term"

type 'a converter = {
  constc : local_theory -> term -> (term -> 'a) -> term -> 'a,
  funcc : local_theory -> term -> (term -> 'a) -> term -> term list -> 'a,
  ifc : local_theory -> term -> (term -> 'a) -> term -> term -> term -> 'a,
  casec : local_theory -> term -> (term -> 'a) -> term -> term list -> 'a
};

(* Count number of arguments needed for a function *)

(* Walks over term and calls given converter *)
fun walk_func (t1 $ t2) ts = walk_func t1 (t2::ts)
  | walk_func t ts = (t, ts)
fun build_func (f, []) = f
  | build_func (f, (t::ts)) = build_func (f$t, ts)
fun walk ctxt origin (conv as {ifc, casec, funcc, ...}) (t as _ $ _) =
  let
    val (f, args) = walk_func t []
    val this = (walk ctxt origin conv)
    val _ = (case f of Abs _ => error "Lambdas are not allowed" | _ => ())
  in
    (if is_if f then
      (case args of [cond, t, f] => ifc ctxt origin this cond t f
                  | _ => error "Partial applications not allowed (if)")
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
    | _ => error "Could not fix variables")
  | casecAbs _ f n _ t = f (casecBuildBounds n t)
fun fixCasecCases _ _ _ [t] = [t]
  | fixCasecCases ctxt f (Type (_,[T,Tr])) (t::ts) = casecAbs ctxt f 0 T t :: fixCasecCases ctxt f Tr ts
  | fixCasecCases _ _ _ _ = error "Invalid case types/terms"
fun fixCasec ctxt _ f (t as Const (n,T)) args =
      (check_args "cases" (Syntax.read_term ctxt n,args); build_func (t,fixCasecCases ctxt f T args))
  | fixCasec _ _ _ _ _ = error "Invalid case term"
fun fixPartTerms ctxt term (pT $ (eq $ l $ r)) =
  let
    val _ = check_args "args" (walk_func l [])
  in
    pT $ (eq $ l $ (walk ctxt term {
          funcc = (fn _ => fn _ => fn f => fn t => fn args =>
              (check_args "func" (t,args); build_func (t, map f args))),
          constc = (fn _ => fn _ => fn _ => fn c => c),
          ifc = (fn _ => fn _ => fn f => fn cond => fn tt => fn tf =>
            ((Const ("HOL.If", @{typ "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"})) $ f cond $ (f tt) $ (f tf))),
          casec = fixCasec
      } r))
  end
  | fixPartTerms _ _ _ = error "Invalid term to fix"

(* 2. Check for undefined timing functions *)
fun right_of_equation (_ $ (_ $ _ $ r)) = r
  | right_of_equation _ = error "Invalid equation"
(* Returns list of all function without a defined timing function *)
fun check_fun ctxt origin f (func as Const (nm,T)) args =
let
  val name_origin = origin |> dest_Const |> fst
  val f_args = List.foldr (List.@) [] (map f args)
in
  if nm = name_origin orelse Trivial_Funcs.is_trivial (Proof_Context.theory_of ctxt) (nm,T) then f_args else
      case time_term ctxt func of SOME _ => f_args
                                | NONE => func :: f_args
end
  | check_fun _ _ _ _ _ = error "Invalid function"
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
fun fun_to_time ctxt origin (func as Const (nm,T)) =
let
  val timing_name_origin = "T_" ^ Term.term_name origin
  val full_name_origin = origin |> dest_Const |> fst
in
  if nm = full_name_origin then SOME (Free (timing_name_origin, change_typ T)) else
  if Trivial_Funcs.is_trivial (Proof_Context.theory_of ctxt) (nm,T) then NONE else
    time_term ctxt func
end
  | fun_to_time _ _ _ = error "Invalid function to convert"

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
  | casecArgs _ _ = error "Invalid case term"
fun casecIsCase (Type (n1, [_,Type (n2, _)])) = (n1 = "fun" andalso n2 = "fun")
  | casecIsCase _ = false
fun casecLastTyp (Type (n, [T1,T2])) = Type (n, [T1, change_typ T2])
  | casecLastTyp _ = error "Invalid case type"
fun casecTyp (Type (n, [T1, T2])) =
      Type (n, [change_typ T1, (if casecIsCase T2 then casecTyp else casecLastTyp) T2])
  | casecTyp _ = error "Invalid case type"
fun casec _ _ f (Const (t,T)) args =
  if not (casecIsCase T) then error "Invalid case type" else
    plus (build_func (Const (t,casecTyp T), casecArgs f args)) (f (List.last args))
  | casec _ _ _ _ _ = error "Invalid case term"
val converter : term converter = {
        constc = fn _ => fn _ => fn _ => fn _ => one,
        funcc = funcc,
        ifc = ifc,
        casec = casec
    }
fun top_converter _ _ = plus one

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
fun acasecAbs f (Abs (v,Ta,t)) = (case acasecAbs f t of (nconst,t) => (nconst,Abs (v,Ta,t)))
  | acasecAbs f t = (case f t of NONE => (false,zero) | SOME t => (true,t))
fun acasecArgs _ [t] = (false, [t])
  | acasecArgs f (t::ar) =
    (case acasecAbs f t of (nconst, tt) => 
      acasecArgs f ar ||> (fn ar => tt :: ar) |>> (if nconst then K true else I))
  | acasecArgs _ _ = error "Invalid case term"
fun acasec _ _ f (Const (t,T)) args =
  if not (casecIsCase T) then error "Invalid case type" else
    let val (nconst, args') = acasecArgs f args in
      aplus
        (if nconst then
          SOME (build_func (Const (t,casecTyp T), args'))
         else NONE)
        (f (List.last args))
    end
  | acasec _ _ _ _ _ = error "Invalid case term"
val aconverter : term option converter = {
        constc = fn _ => fn _ => fn _ => fn _ => NONE,
        funcc = afuncc,
        ifc = aifc,
        casec = acasec
    }
fun atop_converter _ _ = opt_term o (aplus (SOME one))

(* Use converter to convert right side of a term *)
fun to_time ctxt origin converter top_converter term = 
  top_converter ctxt origin (walk ctxt origin converter term)

(* Converts a term to its running time version *)
fun convert_term ctxt origin conv topConv (pT $ (Const (eqN, _) $ l $ r)) =
      pT
      $ (Const (eqN, @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"})
        $ (build_func ((walk_func l []) |>> (fun_to_time ctxt origin) |>> Option.valOf))
        $ (to_time ctxt origin conv topConv r))
  | convert_term _ _ _ _ _ = error "Invalid term to convert"

(* Tactic to prove "f_dom n" *)
fun time_dom_tac ctxt induct_rule domintros =
  (Induction.induction_tac ctxt true [] [[]] [] (SOME [induct_rule]) []
      THEN_ALL_NEW ((K (auto_tac ctxt)) THEN' (fn i => FIRST' (
        (if i <= length domintros then [Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt [List.nth (domintros, i-1)]] else []) @
        [Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt domintros]) i)))

(* Convert given function into a timing function *)
fun reg_time_func (theory: theory) (term: term) conv topConv  print =
  let
    val lthy = Named_Target.theory_init theory
    val _ =
      case time_term lthy term
        of SOME _ => error "Timing function already declared"
         | NONE => ()

    val info = SOME (Function.get_info lthy term) handle Empty => NONE
    val terms = case info of
          SOME i => terms_of_info i
        | _ => Spec_Rules.retrieve lthy term
                |> hd
                |> #rules
                |> map Thm.prop_of
    val is_partial = case info of SOME {is_partial, ...} => is_partial | _ => false

    (* 1. Fix all terms *)
    (* Exchange Var in types and terms to Free *)
    val terms = map (map_aterms fixTerms #> map_types (map_atyps fixTypes) #> fixPartTerms lthy term) terms

    (* 2. Find missing functions and define them *)
    val missing_funcs = find_missing lthy term (map right_of_equation terms)
    val theory = Local_Theory.exit_global lthy
    val theory = List.foldr (fn (f, ctxt) => reg_time_func ctxt f conv topConv print |> snd) theory missing_funcs
    val lthy = Named_Target.theory_init theory
    
    (* 3. Convert every equation
      - Change type of toplevel equation from _ \<Rightarrow> _ \<Rightarrow> bool to nat \<Rightarrow> nat \<Rightarrow> bool
      - On left side change name of function to timing function
      - Convert right side of equation with conversion schema
    *)
    val timing_terms = map (convert_term lthy term conv topConv) terms

    (* 4. Register function and prove termination *)
    val name = Term.term_name term
    val timing_name = fun_name_to_time name
    val bindings = [(Binding.name timing_name, NONE, NoSyn)]
    val fun_config = Function_Common.FunctionConfig
      {sequential=false, default=NONE, domintros=true, partials=is_partial}
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
    val specs = map (fn eq => (((Binding.empty, []), eq), [], [])) timing_terms
    
    (* Register function *)
    val (_, lthy) =
      Function.add_function bindings specs fun_config pat_completeness_auto lthy

    (* Start proving the termination *)
    fun args (a$_) = args a |> (fn (x,ar) => (x^"x",x::ar))
      | args _ = ("x",[])
    val dom_args = (case terms of ((_ $ (_ $ l $ _))::_) => args l |> snd | _ => error "Invalid function")
    
    val lthy' = Named_Target.theory_init (Local_Theory.exit_global lthy)
  
    (* Proof by lexicographic_order_tac *)
    val (time_info, lthy'') =
      (Function.prove_termination NONE
        (Lexicographic_Order.lexicographic_order_tac false lthy') lthy')
        handle (ERROR _) => 
        let
          val _ = warning "Falling back to proof over dom..."

          val {inducts, ...} = case info of SOME i => i | _ => error "No inducts available"
          val induct = (Option.valOf inducts |> hd)

          val domintros = Proof_Context.get_fact lthy' (Facts.named (timing_name ^ ".domintros"))
          val prop = (timing_name ^ "_dom (" ^ (String.concatWith "," dom_args) ^ ")")
                      |> Syntax.read_prop lthy'
          (* Prove a helper lemma *)
          val dom_lemma = Goal.prove lthy' dom_args [] prop
            (fn {context, ...} => HEADGOAL (time_dom_tac context induct domintros))
          (* Add dom_lemma to simplification set *)
          val simp_lthy = Simplifier.add_simp dom_lemma lthy'
      
          (* Use lemma to prove termination *)
        in
          Function.prove_termination NONE
            (auto_tac simp_lthy) lthy'
        end
    
    (* Context for printing without showing question marks *)
    val print_ctxt = Config.put show_question_marks false lthy''
    (* Print result if print *)
    val _ = if not print then () else case info of
        SOME info => print_timing print_ctxt info time_info
      | NONE =>
        let
          val (nm,T) = case term of Const t => t | _ => error "Invalid term"
        in
          print_timing' print_ctxt { name=nm, terms=terms, typ=T } (info_pfunc time_info)
        end
  in
    (time_info, Local_Theory.exit_global lthy'')
  end;

(* Convert function into its timing function (called by command) *)
fun reg_time_func_cmd func conv topConv (theory: theory) =
let
  val fterm = Syntax.read_term (Proof_Context.init_global theory) func
  val (_, theory') = reg_time_func theory fterm conv topConv true
in theory'
end;

val _ = Outer_Syntax.command @{command_keyword "define_time_fun"}
  "Defines runtime function of a function"
  (Parse.prop >> (fn func => Toplevel.theory (reg_time_func_cmd func converter top_converter)));
val _ = Outer_Syntax.command @{command_keyword "define_atime_fun"}
  "Defines asymptotic runtime function of a function"
  (Parse.prop >> (fn func => Toplevel.theory (reg_time_func_cmd func aconverter atop_converter)));

end

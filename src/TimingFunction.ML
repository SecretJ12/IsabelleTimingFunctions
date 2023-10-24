fun to_time t = t

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

    fun fixTerms (Var(ixn,T)) = Free (fst ixn, T)
      | fixTerms (c as Const(nm,T)) = if member (op=) [full_name] nm then Free (timing_name,T) else c
      | fixTerms t = t
    fun fixTypes (TVar ((t, _), T)) = TFree (t, T)
      | fixTypes t = t
    fun parseTerms ((Const pT) $ (eq $ l $ r)) = (Const pT) $ (eq $ l $ to_time r)
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

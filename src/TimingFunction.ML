fun separate sep prts =
  flat (Library.separate [Pretty.str sep] (map single prts));

fun terms_of_info (info: Function.info) =
let
  val {simps, ...} = info;
in
  map Thm.prop_of (case simps of SOME s => s | NONE => [])
end;

fun print_fun ctxt title (info: Function.info) =
let
  val {defname, fs, ...} = info;
  val name = Binding.name_of defname;
  val typ = (case fs of (Const (_, typ)::_) => typ | _ => raise Fail "Type of function not implemented")
  val trms = terms_of_info info;
  val header_beg = Pretty.str ("fun " ^ name ^ " :: ");
  val header_end = Pretty.str (" where\n  ");
  val header = [header_beg, Pretty.quote (Syntax.pretty_typ ctxt typ), header_end];
  val ptrms = (separate "\n| " (map (Syntax.pretty_term ctxt) trms));
  val lines = header @ ptrms;
in
  Pretty.writeln (Pretty.text_fold [Pretty.str (title ^ "\n"), Pretty.item lines])
end;

fun transform_info ({add_simps, case_names, fnames, fs, R, dom, psimps, pinducts,
  simps, inducts, termination, totality, defname, is_partial, cases, pelims, elims} : Function.info) =
    let
      fun name n = Binding.make ("T_" ^ Binding.name_of n, Position.none)
      fun conv thm = thm
    in
      { add_simps = add_simps, case_names = case_names, fnames = map name fnames,
        fs = fs, R = R, dom = dom, psimps = psimps,
        pinducts = pinducts, simps = Option.map (fn s => map conv s) simps,
        inducts = inducts, termination = termination,
        totality = totality, defname = name defname,
        is_partial = is_partial, cases = cases,
        pelims = pelims, elims = elims }
    end

fun func_to_time (info: Function.info) =
  transform_info info;

fun register_time_func theory (info: Function.info) =
  theory |> Local_Theory.declaration {syntax = false, pervasive = false, pos = \<^here>}
          (fn phi => Function_Common.add_function_data (Function_Common.transform_function_data phi info));

fun convert func (lthy: local_theory) =
let
val ctxt = Config.put show_question_marks false lthy
val info = Function.get_info lthy (Syntax.read_term lthy func)
val time_info = func_to_time info
in (print_fun ctxt "Original function:" info; print_fun ctxt "Timing function:" time_info; register_time_func lthy time_info)
end;

Outer_Syntax.local_theory @{command_keyword "define_time_fun"}
"Defines runtime function of a function"
  (Parse.prop >> (fn func => convert func));



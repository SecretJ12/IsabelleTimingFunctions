fun print_cases cases =
  (case cases of [] => () | (x::xs) => (tracing x; print_cases xs));

fun separate sep prts =
  flat (Library.separate [Pretty.str sep] (map single prts));

fun print_fun ctxt (info: Function.info) =
let
  val {defname, fs, simps, ...} = info;
  val name = Binding.name_of defname;
  val (t::_) = fs;
  val Const (_, typ) = t;
  val trms = map Thm.prop_of (case simps of SOME s => s | NONE => []);
  val header_beg = Pretty.str ("fun " ^ name ^ " :: \"");
  val header_end = Pretty.str ("\" where\n  ");
  val header = [header_beg, Syntax.pretty_typ ctxt typ, header_end];
  val ptrms = (separate "\n| " (map (Syntax.pretty_term ctxt) trms));
  val lines = header @ ptrms;
in
  Pretty.writeln (Pretty.text_fold lines)
end;

fun convert thm_name func theory =
let
val ctxt = Proof_Context.init_global theory;
val no_q_ctxt = Config.put show_question_marks false ctxt
val info = Function.get_info ctxt (Syntax.read_term ctxt func)
in (print_fun no_q_ctxt info; theory)
end;

Outer_Syntax.local_theory @{command_keyword "define_time_fun"}
"Defines runtime function of a function"
  (Parse_Spec.simple_spec >> (fn ((thm_name, _), func) => Local_Theory.background_theory (convert thm_name func)))
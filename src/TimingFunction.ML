fun print_cases cases =
  (case cases of [] => () | (x::xs) => (tracing x; print_cases xs));

fun convert thm_name func theory =
let
val ctxt = Proof_Context.init_global theory;
val {case_names, ...} = Function.get_info ctxt (Syntax.read_term ctxt func)
in (tracing ("cases of " ^ func ^ ":"); print_cases case_names; theory)
end;

Outer_Syntax.local_theory @{command_keyword "define_time_fun"}
"Defines runtime function of a function"
  (Parse_Spec.simple_spec >> (fn ((thm_name, _), func) => Local_Theory.background_theory (convert thm_name func)))
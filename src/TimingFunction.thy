theory TimingFunction
  imports Main
  keywords "define_time_fun" :: thy_decl
begin

ML \<open>
fun convert ((thm_name, _), str) = 
    Local_Theory.background_theory (fn ctxt => (thm_name; tracing str; ctxt));

Outer_Syntax.local_theory @{command_keyword "define_time_fun"}
"Defines runtime function of a function"
  (Parse_Spec.simple_spec >> convert)
\<close>

define_time_fun T_test: test

end
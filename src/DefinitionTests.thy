theory DefinitionTests
  imports Main
  keywords "do_it" :: thy_decl
begin

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map f [] = []"
| "map f (x#xs) = f x # map f xs"

fun T2_map :: "(('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> nat)) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "T2_map f [] = 1"
| "T2_map f (x#xs) = snd f x + T2_map f xs + 1"

ML \<open>
fun define ctxt =
  let
  val def = Binding.name ("T_map_def")
  val eq = @{term "T_map f xs = T2_map (undefined::'a \<Rightarrow> nat,f) xs"} |> HOLogic.mk_Trueprop
  val ctxt' = Specification.definition NONE [] [] ((def, []), eq) ctxt

  val f = Token.make_string0 "f"
  val xs = Token.make_string0 "xs"
  val src = Token.make_src ("??", Position.none) [f, xs]

  val def = Binding.name ("T_map_def")
  val name = Binding.name "T_map"
  val rhs = @{term "(\<lambda>f xs. T2_map (undefined::'a \<Rightarrow> nat,f) xs)"}
  val ctxt'' = Local_Theory.define ((name, NoSyn), ((def, []), rhs)) ctxt
  in
    ctxt'' |> snd
  end

val _ = Outer_Syntax.local_theory @{command_keyword "do_it"}
    "traces a proposition"
    (Scan.succeed define)
\<close>

do_it
thm T_map_def

end
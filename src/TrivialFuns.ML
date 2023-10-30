
structure TrivialFuns = Theory_Data(
  type T = Symtab.set
  val empty = Symtab.empty
  val merge = Symtab.merge (K true));

fun add_trivial f = TrivialFuns.map (Symtab.insert_set f);
fun is_trivial_decl lthy f = Option.isSome ((Symtab.lookup o TrivialFuns.get) lthy f);
val print_trivial = TrivialFuns.get

fun save func thy =
let
val fterm = Syntax.read_term (Proof_Context.init_global thy) func;
val name = (case fterm of Const (n,_) => n | _ => raise Fail "Invalid function")
val _ = writeln ("Adding \"" ^ name ^ "\" to trivial functions")
in add_trivial name thy
end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>define_time_trivial\<close> "ML setup for global theory"
    (Parse.prop >> (Toplevel.theory o save));
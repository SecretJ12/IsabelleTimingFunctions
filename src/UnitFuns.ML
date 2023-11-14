signature TRIVIAL_FUNCS =
sig

val is_trivial : theory -> string * typ -> bool

end

structure Trivial_Funcs : TRIVIAL_FUNCS =
struct

fun get_constrs thy (Type (n, _)) = these (BNF_LFP_Compat.get_constrs thy n)
  | get_constrs _ _ = []
(* returns if something is a constructor (found in smt_normalize.ML) *)
fun is_constr thy (n, T) =
    let fun match (m, U) = m = n andalso Sign.typ_instance thy (T, U)
    in can (the o find_first match o get_constrs thy o Term.body_type) T end


structure TrivialFuns = Theory_Data(
  type T = Symtab.set
  val empty = Symtab.empty
  val merge = Symtab.merge (K true));

fun add_trivial f = TrivialFuns.map (Symtab.insert_set f);
fun is_trivial_decl lthy f = Option.isSome ((Symtab.lookup o TrivialFuns.get) lthy f);
(* Trivial should be everything which is a constructor or something like a constant or variable *)
fun is_trivial ctxt (n, (T as Type (Tn,_))) = (Tn <> "fun" orelse is_constr ctxt (n, T) orelse is_trivial_decl ctxt n)
  | is_trivial _ _  = false

fun save func thy =
let
val fterm = Syntax.read_term (Proof_Context.init_global thy) func;
val name = (case fterm of Const (n,_) => n | _ => raise Fail "Invalid function")
val _ = writeln ("Adding \"" ^ name ^ "\" to trivial functions")
in add_trivial name thy
end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>define_time_unit\<close> "ML setup for global theory"
    (Parse.prop >> (Toplevel.theory o save));

end
(*  Title:      checker.ML
    Author:     Fabian Huch

Glue-code for the Metalogic Proof Checker.
*)

signature CHECKER = sig
  (* primitives *)
  type int
  type nat
  type class
  type sort
  type name
  val int: IntInf.int -> int
  val nat: IntInf.int -> nat
  val class: string -> class
  val sort: string list -> sort
  val name: string -> name

  (* types *)
  datatype var = Free of string | Var of (string * int)
  datatype typ = Ty of name * typ list | Tv of var * sort
  datatype term =
    Ct of name * typ | Fv of var * typ | Bv of nat | Abs of typ * term | App of term * term
  datatype proofterm =
     PAxm of term * ((var * sort) * typ) list
   | PBound of nat
   | Abst of typ * proofterm
   | AbsP of term * proofterm
   | Appt of proofterm * term
   | AppP of proofterm * proofterm
   | OfClass of typ * string
   | Hyp of term
  val typ: Term.typ -> typ
  val term: Term.term -> term
  val tvars_of: Term.term -> (var * sort) list
  val tsubst: Term.term -> Term.typ list -> ((var * sort) * typ) list
  val proofterm: ((Proofterm.thm_header * Proofterm.thm_body) -> proofterm) -> Proofterm.proof ->
    proofterm

  (* signature *)
  type osig = (class * class) list * (name * (class * sort list) list) list
  type sign = (name * typ) list * (name * nat) list * osig
  val sign_of: Context.theory -> sign
  type theory = sign * term list
  val theory_of: Context.theory -> theory

  (* checker *)
  val wf_theory: theory -> bool
  val wf_theory_proof: theory -> proofterm -> term -> bool
end

structure Checker : CHECKER = struct
structure C = ExportCheck

type int = C.int
type nat = C.nat
type class = string
type sort = string C.set
type name = string

val int = C.int
val nat = C.nat
val class = I  
val sort = C.sort
val name = I

datatype var = datatype C.variable
datatype typ = datatype C.typ
datatype term = datatype C.term
datatype proofterm = datatype C.proofterm

fun typ T =
  case T of
    Term.Type (a, Ts) => Ty (a, map typ Ts)
  | Term.TFree (x, S) => Tv (Free x, sort S)
  | Term.TVar ((x, i), S) => Tv (Var (x, int i), sort S)

fun term t =
  case t of
    Term.Const (a, T) => Ct (a, typ T)
  | Term.Free (x, T) => Fv (Free x, typ T)
  | Term.Var ((x, i), T) => Fv (Var (x, int i), typ T)
  | Term.Bound i => Bv (nat i)
  | Term.Abs (_, T, t) => Abs (typ T, term t)
  | t1 $ t2 => App (term t1, term t2)

fun tvars_of t = (Term.add_tvars t [] |> rev) |> map (fn ((x, i), S) => (Var (x, int i), sort S))
fun tsubst t Ts = map2 pair (tvars_of t) (map typ Ts)

fun proofterm f prf =
  let
    fun proof prf =
      case prf of
        Proofterm.PBound i => PBound (nat i)
      | Proofterm.Abst (_, SOME T, prf) => Abst (typ T, proof prf)
      | Proofterm.AbsP (_, SOME t, prf) => AbsP (term t, proof prf)
      | prf % SOME t => Appt (proof prf, term t)
      | prf1 %% prf2 => AppP (proof prf1, proof prf2)
      | Proofterm.Hyp t => Hyp (term t)
      | Proofterm.PAxm (_, t, SOME Ts) => PAxm (term t, tsubst t Ts)
      | Proofterm.PClass (T, c) => OfClass (typ T, c)
      | Proofterm.PThm (thm_header as {types = SOME _, ...}, thm_body) => f (thm_header, thm_body)
      | Proofterm.Oracle _ => error "Rejecting oracle proof"
      | _ => error "Ill-formed proof term"
  in proof prf end

type osig = (name * name) list * (name * (class * sort list) list) list
type sign = (name * typ) list * (name * nat) list * osig

fun sign_of thy =
  let
    (* no abbreviations: visible only from journal-paper glue.ML *)
    val const_type =
      thy
      |> Sign.consts_of |> Consts.dest |> #constants 
      |> map_filter (fn (a, (T, NONE)) => SOME (a, typ T) | _ => NONE)
    val tsig = Sign.tsig_of thy
    val types = Type.logical_types tsig
    val type_arity = map (swap o ` (nat o Type.arity_number tsig)) types

    val algebra = Sign.classes_of thy

    (* paper states that Field of sub = set of classes, so sub must be refl *)
    fun class_sub C = map (pair C) (C :: Sorts.super_classes algebra C)

    val sub = Sorts.all_classes algebra |> maps class_sub
    val arities = Sorts.arities_of algebra

    (* Sorts normalized according to paper *)
    val normalize_sorts = C.exenormalize_sort sub o sort

    (* arities for all logical types (including those without class isntances) *)
    val tcs = 
      map (fn a => (a, Symtab.lookup_list arities a |> map (apsnd (map normalize_sorts)))) types
    val osig = (sub, tcs)
  in (const_type, type_arity, osig) end;

type theory = sign * term list

fun theory_of thy =
  (sign_of thy, Thm.all_axioms_of thy |> map (term o Thm.full_prop_of o Thm.unconstrainT o snd))

fun wf_theory (sign, axioms) = C.exe_wf_theory (C.ExeTheory (C.ExeSignature sign, axioms))
fun wf_theory_proof (sign, axioms) proofterm term =
  case C.exereplay (C.ExeTheory (C.ExeSignature sign, axioms)) proofterm of
    NONE => false
  | SOME term1 => C.eq_term term term1

end
(*  Title:      checker.ML
    Author:     Fabian Huch

ML module for the Metalogic Proof 
*)

signature CHECKER_EXPORT =
sig
  (* primitives *)
  type int
  type nat
  type class
  type sort
  type name
  val int: IntInf.int -> int
  val nat: IntInf.int -> nat
  val sort: string list -> sort
  val normalize_sort: (class * class) list -> sort -> sort

  (* types *)
  datatype var = Free of string | Var of (string * int)
  datatype typ = Ty of name * typ list | Tv of var * sort
  datatype term =
    Ct of name * typ | Fv of var * typ | Bv of nat | Abs of typ * term | App of term * term
  type tsubst = ((var * sort) * typ) list
  datatype proof =
     PAxm of term * tsubst
   | PBound of nat
   | Abst of typ * proof
   | AbsP of term * proof
   | Appt of proof * term
   | AppP of proof * proof
   | OfClass of typ * string
   | Hyp of term

  (* theory signature *)
  type osig = (class * class) list * (name * (class * sort list) list) list
  type sign = (name * typ) list * (name * nat) list * osig
  type theory = sign * term list

  (* checker *)
  val wf_theory: theory -> bool
  val wf_theory_replay: theory -> proof -> term option

  (* extra *)
  val eq_term: term * term -> bool
  val eq_Ts: (var * sort) * (var * sort) -> bool
end

(* safe signature *)
signature CHECKER =
sig
  type thm
  val thm: theory -> Thm.thm -> thm
  type pthm = Proofterm.thm_header * Proofterm.thm_body
  val pthm: theory -> pthm -> thm
  type proof
  type cthm
  val proof: (pthm -> cthm) -> thm -> proof
  type cthy
  val cthy: theory -> cthy option
  val extend: cthy -> cthm list -> cthy
  val axiomatize: pthm -> cthm
  val check: cthy -> thm -> proof -> cthm option
end

structure Checker : CHECKER =
struct

structure C: CHECKER_EXPORT = struct
open ExportCheck

type class = string
type sort = string set
type name = string

val normalize_sort = exenormalize_sort

datatype var = datatype variable
datatype proof = datatype proofterm

type tsubst = ((var * sort) * typ) list
type osig = (name * name) list * (name * (class * sort list) list) list
type sign = (name * typ) list * (name * nat) list * osig
type theory = sign * term list

fun wf_theory (sign, axioms) = exe_wf_theory (ExeTheory (ExeSignature sign, axioms))
fun wf_theory_replay (sign, axioms) proofterm =
  exereplay (ExeTheory (ExeSignature sign, axioms)) proofterm
end

fun typ T =
  case T of
    Term.Type (a, Ts) => C.Ty (a, map typ Ts)
  | Term.TFree (x, S) => C.Tv (C.Free x, C.sort S)
  | Term.TVar ((x, i), S) => C.Tv (C.Var (x, C.int i), C.sort S)

fun term t =
  case t of
    Term.Const (a, T) => C.Ct (a, typ T)
  | Term.Free (x, T) => C.Fv (C.Free x, typ T)
  | Term.Var ((x, i), T) => C.Fv (C.Var (x, C.int i), typ T)
  | Term.Bound i => C.Bv (C.nat i)
  | Term.Abs (_, T, t) => C.Abs (typ T, term t)
  | t1 $ t2 => C.App (term t1, term t2)

fun tvars_of t =
  (Term.add_tvars t [] |> rev) |> map (fn ((x, i), S) => (C.Var (x, C.int i), C.sort S))
fun tsubst t Ts = map2 pair (tvars_of t) (map typ Ts)

fun proofterm f prf =
  let
    fun proof prf =
      case prf of
        Proofterm.MinProof => error "Ill-formed proof term: MinProof"
      | Proofterm.PBound i => C.PBound (C.nat i)
      | Proofterm.Abst (_, SOME T, prf) => C.Abst (typ T, proof prf)
      | Proofterm.Abst (_, NONE, _) => error "Ill-formed proof term: Abst NONE"
      | Proofterm.AbsP (_, SOME t, prf) => C.AbsP (term t, proof prf)
      | Proofterm.AbsP (_, NONE, _) => error "Ill-formed proof term: AbsP NONE"
      | prf % SOME t => C.Appt (proof prf, term t)
      | _ % NONE => error "Ill-formed proof term: Appt NONE" 
      | prf1 %% prf2 => C.AppP (proof prf1, proof prf2)
      | Proofterm.Hyp t => C.Hyp (term t)
      | Proofterm.PAxm (_, t, SOME Ts) => C.PAxm (term t, tsubst t Ts)
      | Proofterm.PAxm (_, _, NONE) => error "Ill-formed proof term: PAxm NONE" 
      | Proofterm.PClass (T, c) => C.OfClass (typ T, c)
      | Proofterm.Oracle _ => error "Rejecting oracle proof"
      | Proofterm.PThm (thm_header as {types = SOME _, ...}, thm_body) => f (thm_header, thm_body)
      | Proofterm.PThm ({types = NONE, ...}, _) => error "Ill-formed proof term: PThm NONE"
  in proof prf end

type pthm = Proofterm.thm_header * Proofterm.thm_body
datatype thm = Thm of {t: C.term, Ts: (C.var * C.sort) list, prf: Proofterm.proof}

(* pthm needs variables abstracted *)
fun pthm_term prop =
  let
    val Ts = tvars_of prop (* order needs to be kept *)
    val prop1 = Proofterm.forall_intr_variables_term prop
  in if eq_set C.eq_Ts (Ts, tvars_of prop1) then (term prop1, Ts) else error "TVars changed" end

fun pthm thy ({prop, ...}, thm_body) =
  let
    val (t, Ts) = pthm_term prop
    val prf =
      Proofterm.thm_body_proof_open thm_body
      |> Proofterm.reconstruct_proof thy prop
      |> Proofterm.forall_intr_variables prop
  in Thm {t = t, Ts = Ts, prf = prf} end

fun thm thy thm =
  let 
    val thm1 = thm |> Thm.transfer thy |> Thm.unconstrainT
    val prop = Thm.full_prop_of thm1
  in Thm {t = term prop, Ts = tvars_of prop, prf = Thm.reconstruct_proof_of thm1} end

type proof = C.proof
datatype cthm = Cthm of {t: C.term, Ts: (C.var * C.sort) list}

fun instantiate (Cthm {t, Ts}) ({types, ...}, _) =
  let val Tinst = map typ (the types)
  in C.PAxm (t, Ts ~~ Tinst) end

fun proof f (Thm {prf, ...}) = proofterm (fn pthm => instantiate (f pthm) pthm) prf

datatype cthy = Cthy of {theory: C.theory, axs: cthm list}

fun sign_of thy =
  let
    (* no abbreviations: visible only from journal-paper glue.ML *)
    val const_type =
      thy
      |> Sign.consts_of |> Consts.dest |> #constants 
      |> map_filter (fn (a, (T, NONE)) => SOME (a, typ T) | _ => NONE)
    val tsig = Sign.tsig_of thy
    val types = Type.logical_types tsig
    val type_arity = map (swap o ` (C.nat o Type.arity_number tsig)) types

    val algebra = Sign.classes_of thy

    (* paper states that Field of sub = set of classes, so sub must be refl *)
    fun class_sub C = map (pair C) (C :: Sorts.super_classes algebra C)

    val sub = Sorts.all_classes algebra |> maps class_sub
    val arities = Sorts.arities_of algebra
    val sort = (C.normalize_sort sub) o C.sort

    fun make_tc_sig type_name =
      (type_name, Symtab.lookup_list arities type_name |> map (apsnd (map sort)))

    (* arities for all logical types (including those without class instances) *)
    val tcs = map make_tc_sig types
    val osig = (sub, tcs)
  in (const_type, type_arity, osig) end;

fun theory_of thy =
  (sign_of thy, Thm.all_axioms_of thy |> map (term o Thm.full_prop_of o Thm.unconstrainT o snd))

fun cthy thy =
  let val theory = theory_of thy
  in if C.wf_theory theory then SOME (Cthy {theory = theory, axs = []}) else NONE end

fun extend (Cthy {theory, axs}) thms = Cthy {theory = theory, axs = axs @ thms}

fun axiomatize ({prop, ...}, _) =
  let val (t, Ts) = pthm_term prop
  in Cthm {t = t, Ts = Ts} end

fun check (Cthy {theory = (sign, axs0), axs}) (Thm {t, Ts, ...}) prf =
  let
    val checked = C.wf_theory_replay (sign, axs0 @ (map (fn Cthm {t, ...} => t) axs)) prf
    fun cthm t1 = if C.eq_term (t, t1) then SOME (Cthm {t = t, Ts = Ts}) else NONE
  in checked |> Option.mapPartial cthm end

end
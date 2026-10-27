structure Str_Literal : sig
  type int = IntInf.int
  val literal_of_asciis : int list -> string
  val asciis_of_literal : string -> int list
end = struct

open IntInf;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs; (* deliberate clone not relying on List._ structure *)

fun check_ascii k =
  if 0 <= k andalso k < 128
  then k
  else raise Fail "Non-ASCII character in literal";

val char_of_ascii = Char.chr o toInt o (fn k => k mod 128);

val ascii_of_char = check_ascii o fromInt o Char.ord;

val literal_of_asciis = String.implode o map char_of_ascii;

val asciis_of_literal = map ascii_of_char o String.explode;

end;

structure ExportCheck : sig
  type int
  type nat
  type 'a set
  datatype variable = Free of string | Var of (string * int)
  datatype typ = Ty of string * typ list | Tv of variable * string set
  datatype term = Ct of string * typ | Fv of variable * typ | Bv of nat |
    Abs of typ * term | App of term * term
  type num
  datatype proofterm = PAxm of term * ((variable * string set) * typ) list |
    PBound of nat | Abst of typ * proofterm | AbsP of term * proofterm |
    Appt of proofterm * term | AppP of proofterm * proofterm |
    OfClass of typ * string | Hyp of term
  datatype exesignature =
    ExeSignature of
      (string * typ) list * (string * nat) list *
        ((string * string) list *
          (string * (string * string set list) list) list)
  datatype exetheory = ExeTheory of exesignature * term list
  val exereplay : exetheory -> proofterm -> term option
  val exe_wf_sig : exesignature -> bool
  val exe_sig_conds : exesignature -> bool
  val exeis_std_sig : exesignature -> bool
  val exe_wf_theory : exetheory -> bool
  val exe_check_proof : exetheory -> proofterm -> term -> bool
  val int : IntInf.int -> int
  val nat : IntInf.int -> nat
  val norm : term -> term option
  val sort : string list -> string set
  val vars : term -> (variable * typ) list
  val eq_typ : typ -> typ -> bool
  val eq_var : variable -> variable -> bool
  val eq_term : term -> term -> bool
  val term_ok : exesignature -> term -> bool
  val type_of : term -> typ option
  val of_class : typ -> string -> term
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

datatype 'a set = Set of 'a list | Coset of 'a list;

fun eq A_ a b = equal A_ a b;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Set xs) = membera A_ xs x
  | member A_ x (Coset xs) = not (membera A_ xs x);

fun less_eq_set A_ (Set xs) b = list_all (fn x => member A_ x b) xs
  | less_eq_set A_ a (Coset ys) = list_all (fn y => not (member A_ y a)) ys
  | less_eq_set A_ (Coset []) (Set []) = false;

fun equal_seta A_ a b = less_eq_set A_ a b andalso less_eq_set A_ b a;

fun equal_set A_ = {equal = equal_seta A_} : 'a set equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

datatype variable = Free of string | Var of (string * int);

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

fun equal_variablea (Free x1) (Var x2) = false
  | equal_variablea (Var x2) (Free x1) = false
  | equal_variablea (Var x2) (Var y2) =
    equal_proda equal_literal equal_int x2 y2
  | equal_variablea (Free x1) (Free y1) = ((x1 : string) = y1);

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

datatype typ = Ty of string * typ list | Tv of variable * string set;

fun equal_typ () = {equal = equal_typa} : typ equal
and equal_typa (Ty (x11, x12)) (Tv (x21, x22)) = false
  | equal_typa (Tv (x21, x22)) (Ty (x11, x12)) = false
  | equal_typa (Tv (x21, x22)) (Tv (y21, y22)) =
    equal_variablea x21 y21 andalso equal_seta equal_literal x22 y22
  | equal_typa (Ty (x11, x12)) (Ty (y11, y12)) =
    ((x11 : string) = y11) andalso equal_lista (equal_typ ()) x12 y12;
val equal_typ = equal_typ ();

datatype term = Ct of string * typ | Fv of variable * typ | Bv of nat |
  Abs of typ * term | App of term * term;

fun equal_terma (Abs (x41, x42)) (App (x51, x52)) = false
  | equal_terma (App (x51, x52)) (Abs (x41, x42)) = false
  | equal_terma (Bv x3) (App (x51, x52)) = false
  | equal_terma (App (x51, x52)) (Bv x3) = false
  | equal_terma (Bv x3) (Abs (x41, x42)) = false
  | equal_terma (Abs (x41, x42)) (Bv x3) = false
  | equal_terma (Fv (x21, x22)) (App (x51, x52)) = false
  | equal_terma (App (x51, x52)) (Fv (x21, x22)) = false
  | equal_terma (Fv (x21, x22)) (Abs (x41, x42)) = false
  | equal_terma (Abs (x41, x42)) (Fv (x21, x22)) = false
  | equal_terma (Fv (x21, x22)) (Bv x3) = false
  | equal_terma (Bv x3) (Fv (x21, x22)) = false
  | equal_terma (Ct (x11, x12)) (App (x51, x52)) = false
  | equal_terma (App (x51, x52)) (Ct (x11, x12)) = false
  | equal_terma (Ct (x11, x12)) (Abs (x41, x42)) = false
  | equal_terma (Abs (x41, x42)) (Ct (x11, x12)) = false
  | equal_terma (Ct (x11, x12)) (Bv x3) = false
  | equal_terma (Bv x3) (Ct (x11, x12)) = false
  | equal_terma (Ct (x11, x12)) (Fv (x21, x22)) = false
  | equal_terma (Fv (x21, x22)) (Ct (x11, x12)) = false
  | equal_terma (App (x51, x52)) (App (y51, y52)) =
    equal_terma x51 y51 andalso equal_terma x52 y52
  | equal_terma (Abs (x41, x42)) (Abs (y41, y42)) =
    equal_typa x41 y41 andalso equal_terma x42 y42
  | equal_terma (Bv x3) (Bv y3) = equal_nata x3 y3
  | equal_terma (Fv (x21, x22)) (Fv (y21, y22)) =
    equal_variablea x21 y21 andalso equal_typa x22 y22
  | equal_terma (Ct (x11, x12)) (Ct (y11, y12)) =
    ((x11 : string) = y11) andalso equal_typa x12 y12;

val equal_term = {equal = equal_terma} : term equal;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun equal_bool false p = not p
  | equal_bool true p = p
  | equal_bool p false = not p
  | equal_bool p true = p;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

val equal_char = {equal = equal_chara} : char equal;

val equal_variable = {equal = equal_variablea} : variable equal;

val ord_literal =
  {less_eq = (fn a => fn b => ((a : string) <= b)),
    less = (fn a => fn b => ((a : string) < b))}
  : string ord;

val preorder_literal = {ord_preorder = ord_literal} : string preorder;

val order_literal = {preorder_order = preorder_literal} : string order;

val linorder_literal = {order_linorder = order_literal} : string linorder;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype proofterm = PAxm of term * ((variable * string set) * typ) list |
  PBound of nat | Abst of typ * proofterm | AbsP of term * proofterm |
  Appt of proofterm * term | AppP of proofterm * proofterm |
  OfClass of typ * string | Hyp of term;

datatype exesignature =
  ExeSignature of
    (string * typ) list * (string * nat) list *
      ((string * string) list *
        (string * (string * string set list) list) list);

datatype exetheory = ExeTheory of exesignature * term list;

fun filtera p [] = []
  | filtera p (x :: xs) = (if p x then x :: filtera p xs else filtera p xs);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Set xs) = Set (inserta A_ x xs)
  | insert A_ x (Coset xs) = Coset (removeAll A_ x xs);

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun sup_set A_ (Set xs) a = fold (insert A_) xs a
  | sup_set A_ (Coset xs) a = Coset (filtera (fn x => not (member A_ x a)) xs);

val bot_set : 'a set = Set [];

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun fva (Ct (uu, uv)) = bot_set
  | fva (Fv (v, t)) =
    insert (equal_prod equal_variable equal_typ) (v, t) bot_set
  | fva (Bv uw) = bot_set
  | fva (Abs (ux, body)) = fva body
  | fva (App (t, u)) =
    sup_set (equal_prod equal_variable equal_typ) (fva t) (fva u);

fun fv s = sup_seta (equal_prod equal_variable equal_typ) (image fva s);

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun nth (x :: xs) n =
  (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun zip [] ys = []
  | zip xs [] = []
  | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys;

fun ball (Set xs) p = list_all p xs;

fun lift (Bv i) n = (if less_eq_nat n i then Bv (plus_nat i one_nat) else Bv i)
  | lift (Abs (t, body)) n = Abs (t, lift body (plus_nat n one_nat))
  | lift (App (f, t)) n = App (lift f n, lift t n)
  | lift (Ct (v, va)) n = Ct (v, va)
  | lift (Fv (v, va)) n = Fv (v, va);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun name (Free n) = n
  | name (Var (n, uu)) = n;

fun decr lev (Bv i) =
  (if less_eq_nat lev i then Bv (minus_nat i one_nat) else Bv i)
  | decr lev (Abs (ta, t)) = Abs (ta, decr (plus_nat lev one_nat) t)
  | decr lev (App (t, u)) = App (decr lev t, decr lev u)
  | decr uu (Ct (v, va)) = Ct (v, va)
  | decr uu (Fv (v, va)) = Fv (v, va);

fun union A_ = fold (inserta A_);

fun filter p (Set xs) = Set (filtera p xs);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun size_list xs = length_tailrec xs zero_nat;

fun lookup uu [] = NONE
  | lookup f ((x, y) :: xs) = (if f x then SOME y else lookup f xs);

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun assoc_match (Tv (v, s)) t subs =
  (case lookup
          (fn x =>
            equal_proda equal_variable (equal_set equal_literal) x (v, s))
          subs
    of NONE => SOME (((v, s), t) :: subs)
    | SOME u => (if equal_typa u t then SOME subs else NONE))
  | assoc_match (Ty (a, ts)) (Ty (b, us)) subs =
    (if ((a : string) = b) andalso equal_nata (size_list ts) (size_list us)
      then fold (fn (t, u) => fn subsa => bind subsa (assoc_match t u))
             (zip ts us) (SOME subs)
      else NONE)
  | assoc_match (Ty (v, va)) (Tv (vb, vc)) subs =
    (if equal_typa (Ty (v, va)) (Tv (vb, vc)) then SOME subs else NONE);

fun is_none NONE = true
  | is_none (SOME x) = false;

fun tinstT t1 t2 = not (is_none (assoc_match t2 t1 []));

fun typ_of1 uu (Ct (uv, t)) = SOME t
  | typ_of1 ts (Bv i) =
    (if less_nat i (size_list ts) then SOME (nth ts i) else NONE)
  | typ_of1 uw (Fv (ux, t)) = SOME t
  | typ_of1 ts (Abs (t, body)) =
    bind (typ_of1 (t :: ts) body) (fn x => SOME (Ty ("fun", [t, x])))
  | typ_of1 ts (App (t, u)) =
    bind (typ_of1 ts u)
      (fn ua =>
        bind (typ_of1 ts t)
          (fn a =>
            (case a of Ty (_, []) => NONE | Ty (_, [_]) => NONE
              | Ty (funa, [t1, t2]) =>
                (if ((funa : string) = "fun")
                  then (if equal_typa t1 ua then SOME t2 else NONE) else NONE)
              | Ty (_, _ :: _ :: _ :: _) => NONE | Tv (_, _) => NONE)));

fun typ_of t = typ_of1 [] t;

fun bind_fv2 vT n (Fv (v, t)) =
  (if equal_proda equal_variable equal_typ vT (v, t) then Bv n else Fv (v, t))
  | bind_fv2 vT n (Abs (ta, t)) = Abs (ta, bind_fv2 vT (plus_nat n one_nat) t)
  | bind_fv2 vT n (App (f, u)) = App (bind_fv2 vT n f, bind_fv2 vT n u)
  | bind_fv2 uu uv (Ct (v, va)) = Ct (v, va)
  | bind_fv2 uu uv (Bv v) = Bv v;

fun bind_fv vT t = bind_fv2 vT zero_nat t;

fun mk_type ty = Ct ("Pure.type", Ty ("itself", [ty]));

fun incr_bv inc n (Bv i) =
  (if less_eq_nat n i then Bv (plus_nat i inc) else Bv i)
  | incr_bv inc n (Abs (t, body)) =
    Abs (t, incr_bv inc (plus_nat n one_nat) body)
  | incr_bv inc n (App (f, t)) = App (incr_bv inc n f, incr_bv inc n t)
  | incr_bv uu uv (Ct (v, va)) = Ct (v, va)
  | incr_bv uu uv (Fv (v, va)) = Fv (v, va);

fun class_leq A_ B_ sub c1 c2 = member (equal_prod A_ B_) (c1, c2) sub;

fun sort_leq A_ B_ sub s1 s2 =
  ball s2 (fn c_2 => bex s1 (fn c_1 => class_leq A_ B_ sub c_1 c_2));

fun subst_bv2 (Bv i) n u =
  (if less_nat i n then Bv i
    else (if equal_nata i n then u else Bv (minus_nat i one_nat)))
  | subst_bv2 (Abs (t, body)) n u =
    Abs (t, subst_bv2 body (plus_nat n one_nat) (lift u zero_nat))
  | subst_bv2 (App (f, t)) n u = App (subst_bv2 f n u, subst_bv2 t n u)
  | subst_bv2 (Ct (v, va)) uu uv = Ct (v, va)
  | subst_bv2 (Fv (v, va)) uu uv = Fv (v, va);

fun subst_bv u t = subst_bv2 t zero_nat u;

fun distinct A_ [] = true
  | distinct A_ (x :: xs) = not (membera A_ xs x) andalso distinct A_ xs;

fun betapply (Abs (uu, t)) u = subst_bv u t
  | betapply (Ct (v, va)) u = App (Ct (v, va), u)
  | betapply (Fv (v, va)) u = App (Fv (v, va), u)
  | betapply (Bv v) u = App (Bv v, u)
  | betapply (App (v, va)) u = App (App (v, va), u);

fun loose_bvar1 (Bv i) k = equal_nata i k
  | loose_bvar1 (App (t, u)) k = loose_bvar1 t k orelse loose_bvar1 u k
  | loose_bvar1 (Abs (uu, t)) k = loose_bvar1 t (plus_nat k one_nat)
  | loose_bvar1 (Ct (v, va)) uw = false
  | loose_bvar1 (Fv (v, va)) uw = false;

fun is_dependent t = loose_bvar1 t zero_nat;

fun eta_norm (Abs (ta, t)) =
  (case eta_norm t of Ct (literal, typ) => Abs (ta, Ct (literal, typ))
    | Fv (variable, typ) => Abs (ta, Fv (variable, typ))
    | Bv nat => Abs (ta, Bv nat) | Abs (typ, term) => Abs (ta, Abs (typ, term))
    | App (f, Ct (literal, typ)) => Abs (ta, App (f, Ct (literal, typ)))
    | App (f, Fv (variable, typ)) => Abs (ta, App (f, Fv (variable, typ)))
    | App (f, Bv n) =>
      (if equal_nata n zero_nat
        then (if is_dependent f then Abs (ta, App (f, Bv zero_nat))
               else decr zero_nat (eta_norm f))
        else Abs (ta, App (f, Bv (suc (minus_nat n one_nat)))))
    | App (f, Abs (typ, term)) => Abs (ta, App (f, Abs (typ, term)))
    | App (f, App (term1b, term2a)) => Abs (ta, App (f, App (term1b, term2a))))
  | eta_norm (App (t, u)) = App (eta_norm t, eta_norm u)
  | eta_norm (Ct (v, va)) = Ct (v, va)
  | eta_norm (Fv (v, va)) = Fv (v, va)
  | eta_norm (Bv v) = Bv v;

fun replicate n x =
  (if equal_nata n zero_nat then []
    else x :: replicate (minus_nat n one_nat) x);

fun hyps (Abst (uu, p)) = hyps p
  | hyps (AbsP (uv, p)) = hyps p
  | hyps (Appt (p, uw)) = hyps p
  | hyps (AppP (p1, p2)) = union equal_term (hyps p1) (hyps p2)
  | hyps (Hyp t) = [t]
  | hyps (PAxm (v, va)) = []
  | hyps (PBound v) = []
  | hyps (OfClass (v, va)) = [];

fun fst (x1, x2) = x1;

fun domain r = image fst r;

fun snd (x1, x2) = x2;

fun range r = image snd r;

fun field A_ r = sup_set A_ (domain r) (range r);

fun of_bool A_ false = zero (zero_zero_neq_one A_)
  | of_bool A_ true = one (one_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);

fun fold_aterms f (App (t, u)) s = fold_aterms f u (fold_aterms f t s)
  | fold_aterms f (Abs (uu, t)) s = fold_aterms f t s
  | fold_aterms f (Ct (v, va)) s = f (Ct (v, va)) s
  | fold_aterms f (Fv (v, va)) s = f (Fv (v, va)) s
  | fold_aterms f (Bv v) s = f (Bv v) s;

fun add_vars x =
  fold_aterms
    (fn xa => fn l =>
      (case xa of Ct (_, _) => l
        | Fv (idn, s) =>
          inserta (equal_prod equal_variable equal_typ) (idn, s) l
        | Bv _ => l | Abs (_, _) => l | App (_, _) => l))
    x;

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun beta_norm (Ct (xa, x)) = SOME (Ct (xa, x))
  | beta_norm (Fv (xa, x)) = SOME (Fv (xa, x))
  | beta_norm (Bv x) = SOME (Bv x)
  | beta_norm (Abs (xa, x)) = map_option (fn a => Abs (xa, a)) (beta_norm x)
  | beta_norm (App (Ct (xa, x), xaa)) =
    (case beta_norm (Ct (xa, x)) of NONE => NONE
      | SOME (Ct (literal, typ)) =>
        map_option (fn a => App (Ct (literal, typ), a)) (beta_norm xaa)
      | SOME (Fv (variable, typ)) =>
        map_option (fn a => App (Fv (variable, typ), a)) (beta_norm xaa)
      | SOME (Bv nat) => map_option (fn a => App (Bv nat, a)) (beta_norm xaa)
      | SOME (Abs (_, body)) => beta_norm (subst_bv xaa body)
      | SOME (App (term1, term2)) =>
        map_option (fn a => App (App (term1, term2), a)) (beta_norm xaa))
  | beta_norm (App (Fv (xa, x), xaa)) =
    (case beta_norm (Fv (xa, x)) of NONE => NONE
      | SOME (Ct (literal, typ)) =>
        map_option (fn a => App (Ct (literal, typ), a)) (beta_norm xaa)
      | SOME (Fv (variable, typ)) =>
        map_option (fn a => App (Fv (variable, typ), a)) (beta_norm xaa)
      | SOME (Bv nat) => map_option (fn a => App (Bv nat, a)) (beta_norm xaa)
      | SOME (Abs (_, body)) => beta_norm (subst_bv xaa body)
      | SOME (App (term1, term2)) =>
        map_option (fn a => App (App (term1, term2), a)) (beta_norm xaa))
  | beta_norm (App (Bv x, xa)) =
    (case beta_norm (Bv x) of NONE => NONE
      | SOME (Ct (literal, typ)) =>
        map_option (fn a => App (Ct (literal, typ), a)) (beta_norm xa)
      | SOME (Fv (variable, typ)) =>
        map_option (fn a => App (Fv (variable, typ), a)) (beta_norm xa)
      | SOME (Bv nat) => map_option (fn a => App (Bv nat, a)) (beta_norm xa)
      | SOME (Abs (_, body)) => beta_norm (subst_bv xa body)
      | SOME (App (term1, term2)) =>
        map_option (fn a => App (App (term1, term2), a)) (beta_norm xa))
  | beta_norm (App (Abs (xa, x), xaa)) = beta_norm (subst_bv xaa x)
  | beta_norm (App (App (xa, x), xaa)) =
    (case beta_norm (App (xa, x)) of NONE => NONE
      | SOME (Ct (literal, typ)) =>
        map_option (fn a => App (Ct (literal, typ), a)) (beta_norm xaa)
      | SOME (Fv (variable, typ)) =>
        map_option (fn a => App (Fv (variable, typ), a)) (beta_norm xaa)
      | SOME (Bv nat) => map_option (fn a => App (Bv nat, a)) (beta_norm xaa)
      | SOME (Abs (_, body)) => beta_norm (subst_bv xaa body)
      | SOME (App (term1, term2)) =>
        map_option (fn a => App (App (term1, term2), a)) (beta_norm xaa));

fun map_types f (Ct (a, t)) = Ct (a, f t)
  | map_types f (Fv (v, t)) = Fv (v, f t)
  | map_types f (Bv i) = Bv i
  | map_types f (Abs (ta, t)) = Abs (f ta, map_types f t)
  | map_types f (App (t, u)) = App (map_types f t, map_types f u);

fun incr_boundvars inc t = incr_bv inc zero_nat t;

fun subst_bvs1 (Bv n) lev args =
  (if less_nat n lev then Bv n
    else (if less_nat (minus_nat n lev) (size_list args)
           then incr_boundvars lev (nth args (minus_nat n lev))
           else Bv (minus_nat n (size_list args))))
  | subst_bvs1 (Abs (t, body)) lev args =
    Abs (t, subst_bvs1 body (plus_nat lev one_nat) args)
  | subst_bvs1 (App (f, t)) lev args =
    App (subst_bvs1 f lev args, subst_bvs1 t lev args)
  | subst_bvs1 (Ct (v, va)) uu uv = Ct (v, va)
  | subst_bvs1 (Fv (v, va)) uu uv = Fv (v, va);

fun subst_bvs args t = subst_bvs1 t zero_nat args;

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun the (SOME x2) = x2;

val eq_elim_ax : term =
  App (App (Ct ("Pure.imp",
                 Ty ("fun",
                      [Ty ("prop", []),
                        Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
             App (App (Ct ("Pure.eq",
                            Ty ("fun",
                                 [the (typ_of
(Fv (Var ("A", zero_int), Ty ("prop", [])))),
                                   Ty ("fun",
[the (typ_of (Fv (Var ("B", zero_int), Ty ("prop", [])))), Ty ("prop", [])])])),
                        Fv (Var ("A", zero_int), Ty ("prop", []))),
                   Fv (Var ("B", zero_int), Ty ("prop", [])))),
        App (App (Ct ("Pure.imp",
                       Ty ("fun",
                            [Ty ("prop", []),
                              Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
                   Fv (Var ("A", zero_int), Ty ("prop", []))),
              Fv (Var ("B", zero_int), Ty ("prop", []))));

val eq_intr_ax : term =
  App (App (Ct ("Pure.imp",
                 Ty ("fun",
                      [Ty ("prop", []),
                        Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
             App (App (Ct ("Pure.imp",
                            Ty ("fun",
                                 [Ty ("prop", []),
                                   Ty ("fun",
[Ty ("prop", []), Ty ("prop", [])])])),
                        Fv (Var ("A", zero_int), Ty ("prop", []))),
                   Fv (Var ("B", zero_int), Ty ("prop", [])))),
        App (App (Ct ("Pure.imp",
                       Ty ("fun",
                            [Ty ("prop", []),
                              Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
                   App (App (Ct ("Pure.imp",
                                  Ty ("fun",
                                       [Ty ("prop", []),
 Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
                              Fv (Var ("B", zero_int), Ty ("prop", []))),
                         Fv (Var ("A", zero_int), Ty ("prop", [])))),
              App (App (Ct ("Pure.eq",
                             Ty ("fun",
                                  [the (typ_of
 (Fv (Var ("A", zero_int), Ty ("prop", [])))),
                                    Ty ("fun",
 [the (typ_of (Fv (Var ("B", zero_int), Ty ("prop", [])))),
   Ty ("prop", [])])])),
                         Fv (Var ("A", zero_int), Ty ("prop", []))),
                    Fv (Var ("B", zero_int), Ty ("prop", [])))));

fun abort_empty_set _ = raise Fail "List.abort_empty_set";

fun maxa A_ (Set []) = abort_empty_set (maxa A_)
  | maxa A_ (Set (x :: xs)) =
    fold (max ((ord_preorder o preorder_order o order_linorder) A_)) xs x;

fun fresh_name s =
  (if equal_seta (equal_list equal_char) s bot_set
    then [Chara (true, false, false, false, false, true, true, false)]
    else replicate (plus_nat (maxa linorder_nat (image size_list s)) one_nat)
           (Chara (true, false, false, false, false, true, true, false)));

fun bit_cut_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), false)
    else let
           val (r, s) =
             IntInf.divMod (IntInf.abs k, IntInf.abs (2 : IntInf.int));
         in
           ((if IntInf.< ((0 : IntInf.int), k) then r
              else IntInf.- (IntInf.~ r, s)),
             ((s : IntInf.int) = (1 : IntInf.int)))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val (_, a) = bit_cut_integer q6;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, a)
                        end;

fun explode s = map char_of_integer (Str_Literal.asciis_of_literal s);

fun mk_of_class ty c =
  App (Ct (implode (explode c @ explode "_class"),
            Ty ("fun", [Ty ("itself", [ty]), Ty ("prop", [])])),
        mk_type ty);

fun fresh_namea s = implode (fresh_name (image explode s));

fun refl_on A_ a r = ball a (fn x => member (equal_prod A_ A_) (x, x) r);

fun mk_all_list l t =
  fold (fn (n, ta) => fn acc =>
         App (Ct ("Pure.all",
                   Ty ("fun",
                        [Ty ("fun", [ta, Ty ("prop", [])]), Ty ("prop", [])])),
               Abs (ta, bind_fv (n, ta) acc)))
    l t;

fun trans_on A_ a r =
  ball r
    (fn (x, y1) =>
      (if member A_ x a
        then (if member A_ y1 a
               then ball r
                      (fn (y2, z) =>
                        (if eq A_ y1 y2
                          then (if member A_ z a
                                 then member (equal_prod A_ A_) (x, z) r
                                 else true)
                          else true))
               else true)
        else true));

fun exefield A_ rel = union A_ (map fst rel) (map snd rel);

fun fv_Proof (PAxm (t, uu)) = fva t
  | fv_Proof (PBound uv) = bot_set
  | fv_Proof (Abst (uw, p)) = fv_Proof p
  | fv_Proof (AbsP (t, p)) =
    sup_set (equal_prod equal_variable equal_typ) (fva t) (fv_Proof p)
  | fv_Proof (Appt (p, t)) =
    sup_set (equal_prod equal_variable equal_typ) (fv_Proof p) (fva t)
  | fv_Proof (AppP (p1, p2)) =
    sup_set (equal_prod equal_variable equal_typ) (fv_Proof p1) (fv_Proof p2)
  | fv_Proof (OfClass (ux, uy)) = bot_set
  | fv_Proof (Hyp t) = fva t;

fun list_all2 p [] ys = null ys
  | list_all2 p xs [] = null xs
  | list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys;

fun minus_list_set A_ xs ys = fold (removeAll A_) ys xs;

fun exesort_ex A_ rel s = ball s (membera A_ (exefield A_ rel));

fun execlass_les A_ cs c1 c2 =
  membera (equal_prod A_ A_) cs (c1, c2) andalso
    not (membera (equal_prod A_ A_) cs (c2, c1));

fun exenormalize_sort cs s =
  filter (fn c => not (bex s (fn ca => execlass_les equal_literal cs ca c))) s;

fun exenormalized_sort cs s =
  equal_seta equal_literal (exenormalize_sort cs s) s;

fun exewf_sort sub s =
  equal_seta equal_literal s bot_set orelse
    exenormalized_sort sub s andalso exesort_ex equal_literal sub s;

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun exesig (ExeTheory (x1, x2)) = x1;

fun execonst_type_of (ExeSignature (x1, x2, x3)) = x1;

fun exetyp_arity_of (ExeSignature (x1, x2, x3)) = x2;

fun exesorts (ExeSignature (x1, x2, x3)) = x3;

fun exetyp_ok_sig sigma (Ty (c, ts)) =
  (case lookup (fn k => ((k : string) = c)) (exetyp_arity_of sigma)
    of NONE => false
    | SOME ar =>
      equal_nata (size_list ts) ar andalso list_all (exetyp_ok_sig sigma) ts)
  | exetyp_ok_sig sigma (Tv (uu, s)) = exewf_sort (fst (exesorts sigma)) s;

fun exeterm_oka sigma (Fv (uu, t)) = exetyp_ok_sig sigma t
  | exeterm_oka sigma (Bv uv) = true
  | exeterm_oka sigma (Ct (s, t)) =
    (case lookup (fn k => ((k : string) = s)) (execonst_type_of sigma)
      of NONE => false | SOME ty => exetyp_ok_sig sigma t andalso tinstT t ty)
  | exeterm_oka sigma (App (t, u)) =
    exeterm_oka sigma t andalso exeterm_oka sigma u
  | exeterm_oka sigma (Abs (ta, t)) =
    exetyp_ok_sig sigma ta andalso exeterm_oka sigma t;

fun exeterm_ok theta t =
  exeterm_oka (exesig theta) t andalso not (is_none (typ_of t));

fun exeaxioms_of (ExeTheory (x1, x2)) = x2;

fun execlass_leq A_ B_ cs c1 c2 = membera (equal_prod A_ B_) cs (c1, c2);

fun exesort_leq A_ B_ sub s1 s2 =
  ball s2 (fn c_2 => bex s1 (fn c_1 => execlass_leq A_ B_ sub c_1 c_2));

fun exehas_sort oss (Tv (uu, sa)) s =
  exesort_leq equal_literal equal_literal (fst oss) sa s
  | exehas_sort oss (Ty (a, ts)) s =
    (case lookup (fn k => ((k : string) = a)) (snd oss) of NONE => false
      | SOME mgd =>
        ball s
          (fn c =>
            (case lookup (fn k => ((k : string) = c)) mgd of NONE => false
              | SOME aa => list_all2 (exehas_sort oss) ts aa)));

fun partial_nth [] uu = NONE
  | partial_nth (x :: xs) n =
    (if equal_nata n zero_nat then SOME x
      else partial_nth xs (minus_nat n one_nat));

fun variant_variable (Free n) s = let
                                    val sa = fresh_namea (image name s);
                                  in
                                    (Free sa, insert equal_variable (Free sa) s)
                                  end
  | variant_variable (Var (n, uu)) s =
    let
      val sa = fresh_namea (image name s);
    in
      (Var (sa, zero_int), insert equal_variable (Var (sa, zero_int)) s)
    end;

fun the_default a NONE = a
  | the_default uu (SOME b) = b;

fun subst_typ insts (Ty (a, ts)) = Ty (a, map (subst_typ insts) ts)
  | subst_typ insts (Tv (idn, s)) =
    the_default (Tv (idn, s))
      (lookup
        (fn x =>
          equal_proda equal_variable (equal_set equal_literal) x (idn, s))
        insts);

fun exereplaya thy uu uv hs (PAxm (t, tis)) =
  (if distinct (equal_prod equal_variable (equal_set equal_literal))
        (map fst tis) andalso
        (list_all (exetyp_ok_sig (exesig thy)) (map snd tis) andalso
          list_all
            (fn (a, b) =>
              let
                val (_, s) = a;
              in
                (fn ta => exehas_sort (exesorts (exesig thy)) ta s)
              end
                b)
            tis) andalso
        exeterm_ok thy t
    then (if membera equal_term (exeaxioms_of thy) t
           then SOME (mk_all_list
                       (minus_list_set (equal_prod equal_variable equal_typ)
                         (add_vars (map_types (subst_typ tis) t) [])
                         (fold add_vars [] []))
                       (map_types (subst_typ tis) t))
           else NONE)
    else NONE)
  | exereplaya thy uw ux hs (PBound n) = partial_nth hs n
  | exereplaya thy vs ns hs (Abst (t, p)) =
    (if exetyp_ok_sig (exesig thy) t
      then let
             val (s, nsa) = variant_variable (Free "default") ns;
           in
             map_option
               (fn ta =>
                 App (Ct ("Pure.all",
                           Ty ("fun",
                                [Ty ("fun", [t, Ty ("prop", [])]),
                                  Ty ("prop", [])])),
                       Abs (t, bind_fv (s, t) ta)))
               (exereplaya thy ((s, t) :: vs) nsa hs p)
           end
      else NONE)
  | exereplaya thy vs ns hs (Appt (p, t)) =
    let
      val rep = exereplaya thy vs ns hs p;
      val ta = subst_bvs (map (fn (a, b) => Fv (a, b)) vs) t;
    in
      (case (rep, typ_of ta) of (NONE, _) => NONE
        | (SOME (Ct (_, _)), _) => NONE | (SOME (Fv (_, _)), _) => NONE
        | (SOME (Bv _), _) => NONE | (SOME (Abs (_, _)), _) => NONE
        | (SOME (App (Ct (_, Ty (_, [])), _)), _) => NONE
        | (SOME (App (Ct (_, Ty (_, Ty (_, []) :: _)), _)), _) => NONE
        | (SOME (App (Ct (_, Ty (_, Ty (_, [_]) :: _)), _)), _) => NONE
        | (SOME (App (Ct (_, Ty (_, [Ty (_, [_, Ty (_, [])])])), _)), _) => NONE
        | (SOME (App (Ct (_, Ty (_, [Ty (_, [_, Ty (_, [])]), Ty (_, [])])),
                       _)),
            NONE)
          => NONE
        | (SOME (App (Ct (s, Ty (fun1,
                                  [Ty (fun2, [tau, Ty (propT1, [])]),
                                    Ty (propT2, [])])),
                       b)),
            SOME taua)
          => (if ((s : string) = "Pure.all") andalso
                   (((fun1 : string) = "fun") andalso
                     (((fun2 : string) = "fun") andalso
                       (((propT1 : string) = "prop") andalso
                         (((propT2 : string) = "prop") andalso
                           (equal_typa tau taua andalso exeterm_ok thy ta)))))
               then SOME (betapply b ta) else NONE)
        | (SOME (App (Ct (_, Ty (_, Ty (_, [_, Ty (_, [])]) ::
                                      Ty (_, []) :: _ :: _)),
                       _)),
            _)
          => NONE
        | (SOME (App (Ct (_, Ty (_, Ty (_, [_, Ty (_, [])]) ::
                                      Ty (_, _ :: _) :: _)),
                       _)),
            _)
          => NONE
        | (SOME (App (Ct (_, Ty (_, Ty (_, [_, Ty (_, [])]) :: Tv (_, _) :: _)),
                       _)),
            _)
          => NONE
        | (SOME (App (Ct (_, Ty (_, Ty (_, _ :: Ty (_, []) :: _ :: _) :: _)),
                       _)),
            _)
          => NONE
        | (SOME (App (Ct (_, Ty (_, Ty (_, _ :: Ty (_, _ :: _) :: _) :: _)),
                       _)),
            _)
          => NONE
        | (SOME (App (Ct (_, Ty (_, Ty (_, _ :: Tv (_, _) :: _) :: _)), _)), _)
          => NONE
        | (SOME (App (Ct (_, Ty (_, Tv (_, _) :: _)), _)), _) => NONE
        | (SOME (App (Ct (_, Tv (_, _)), _)), _) => NONE
        | (SOME (App (Fv (_, _), _)), _) => NONE
        | (SOME (App (Bv _, _)), _) => NONE
        | (SOME (App (Abs (_, _), _)), _) => NONE
        | (SOME (App (App (_, _), _)), _) => NONE)
    end
  | exereplaya thy vs ns hs (AbsP (t, p)) =
    let
      val ta = subst_bvs (map (fn (a, b) => Fv (a, b)) vs) t;
      val rep = exereplaya thy vs ns (ta :: hs) p;
    in
      (if equal_option equal_typ (typ_of ta) (SOME (Ty ("prop", []))) andalso
            exeterm_ok thy ta
        then map_option
               (fn a =>
                 App (App (Ct ("Pure.imp",
                                Ty ("fun",
                                     [Ty ("prop", []),
                                       Ty
 ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
                            ta),
                       a))
               rep
        else NONE)
    end
  | exereplaya thy vs ns hs (AppP (p1, p2)) =
    let
      val rep1 =
        bind (exereplaya thy vs ns hs p1)
          (fn t => map_option eta_norm (beta_norm t));
      val rep2 =
        bind (exereplaya thy vs ns hs p2)
          (fn t => map_option eta_norm (beta_norm t));
    in
      (case (rep1, rep2) of (NONE, _) => NONE | (SOME (Ct (_, _)), _) => NONE
        | (SOME (Fv (_, _)), _) => NONE | (SOME (Bv _), _) => NONE
        | (SOME (Abs (_, _)), _) => NONE
        | (SOME (App (Ct (_, _), _)), _) => NONE
        | (SOME (App (Fv (_, _), _)), _) => NONE
        | (SOME (App (Bv _, _)), _) => NONE
        | (SOME (App (Abs (_, _), _)), _) => NONE
        | (SOME (App (App (Ct (_, Ty (_, [])), _), _)), _) => NONE
        | (SOME (App (App (Ct (_, Ty (_, [Ty (_, [])])), _), _)), _) => NONE
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, []) :: Ty (_, []) :: _)), _),
                       _)),
            _)
          => NONE
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, []) ::
   Ty (_, [Ty (_, [])]) :: _)),
                            _),
                       _)),
            _)
          => NONE
        | (SOME (App (App (Ct (_, Ty (_, [Ty (_, []),
   Ty (_, [Ty (_, []), Ty (_, [])])])),
                            _),
                       _)),
            NONE)
          => NONE
        | (SOME (App (App (Ct (imp, Ty (fn1,
 [Ty (prp1, []), Ty (fn2, [Ty (prp2, []), Ty (prp3, [])])])),
                            a),
                       ba)),
            SOME aa)
          => (if ((imp : string) = "Pure.imp") andalso
                   (((fn1 : string) = "fun") andalso
                     (((fn2 : string) = "fun") andalso
                       (((prp1 : string) = "prop") andalso
                         (((prp2 : string) = "prop") andalso
                           (((prp3 : string) = "prop") andalso
                             equal_terma a aa)))))
               then SOME ba else NONE)
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, []) ::
   Ty (_, [Ty (_, []), Ty (_, [])]) :: _ :: _)),
                            _),
                       _)),
            _)
          => NONE
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, []) ::
   Ty (_, Ty (_, []) :: Ty (_, []) :: _ :: _) :: _)),
                            _),
                       _)),
            _)
          => NONE
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, []) ::
   Ty (_, Ty (_, []) :: Ty (_, _ :: _) :: _) :: _)),
                            _),
                       _)),
            _)
          => NONE
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, []) ::
   Ty (_, Ty (_, []) :: Tv (_, _) :: _) :: _)),
                            _),
                       _)),
            _)
          => NONE
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, []) ::
   Ty (_, Ty (_, _ :: _) :: _) :: _)),
                            _),
                       _)),
            _)
          => NONE
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, []) ::
   Ty (_, Tv (_, _) :: _) :: _)),
                            _),
                       _)),
            _)
          => NONE
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, []) :: Tv (_, _) :: _)), _),
                       _)),
            _)
          => NONE
        | (SOME (App (App (Ct (_, Ty (_, Ty (_, _ :: _) :: _)), _), _)), _) =>
          NONE
        | (SOME (App (App (Ct (_, Ty (_, Tv (_, _) :: _)), _), _)), _) => NONE
        | (SOME (App (App (Ct (_, Tv (_, _)), _), _)), _) => NONE
        | (SOME (App (App (Fv (_, _), _), _)), _) => NONE
        | (SOME (App (App (Bv _, _), _)), _) => NONE
        | (SOME (App (App (Abs (_, _), _), _)), _) => NONE
        | (SOME (App (App (App (_, _), _), _)), _) => NONE)
    end
  | exereplaya thy vs ns hs (OfClass (ty, c)) =
    (if exehas_sort (exesorts (exesig thy)) ty
          (insert equal_literal c bot_set) andalso
          exetyp_ok_sig (exesig thy) ty
      then (case lookup
                   (fn k =>
                     ((k : string) = (implode (explode c @ explode "_class"))))
                   (execonst_type_of (exesig thy))
             of NONE => NONE | SOME (Ty (_, [])) => NONE
             | SOME (Ty (_, Ty (_, []) :: _)) => NONE
             | SOME (Ty (_, [Ty (_, [_])])) => NONE
             | SOME (Ty (funa, [Ty (it, [ity]), Ty (prop, [])])) =>
               (if equal_typa ity (Tv (Var ("'a", zero_int), bot_set)) andalso
                     (((funa : string) = "fun") andalso
                       (((prop : string) = "prop") andalso
                         ((it : string) = "itself")))
                 then SOME (mk_of_class ty c) else NONE)
             | SOME (Ty (_, Ty (_, [_]) :: Ty (_, []) :: _ :: _)) => NONE
             | SOME (Ty (_, Ty (_, [_]) :: Ty (_, _ :: _) :: _)) => NONE
             | SOME (Ty (_, Ty (_, [_]) :: Tv (_, _) :: _)) => NONE
             | SOME (Ty (_, Ty (_, _ :: _ :: _) :: _)) => NONE
             | SOME (Ty (_, Tv (_, _) :: _)) => NONE | SOME (Tv (_, _)) => NONE)
      else NONE)
  | exereplaya thy vs ns hs (Hyp t) =
    (if membera equal_term hs t then SOME t else NONE);

fun exereplay thy p =
  (if list_all
        (fn x =>
          exeterm_ok thy x andalso
            equal_option equal_typ (typ_of x) (SOME (Ty ("prop", []))))
        (hyps p)
    then bind (exereplaya thy []
                (image fst
                  (sup_set (equal_prod equal_variable equal_typ) (fv_Proof p)
                    (fv (Set (hyps p)))))
                (hyps p) p)
           (fn t => map_option eta_norm (beta_norm t))
    else NONE);

val eq_reflexive_ax : term =
  App (App (Ct ("Pure.eq",
                 Ty ("fun",
                      [the (typ_of
                             (Fv (Var ("x", zero_int),
                                   Tv (Var ("'a", zero_int), bot_set)))),
                        Ty ("fun",
                             [the (typ_of
                                    (Fv (Var ("x", zero_int),
  Tv (Var ("'a", zero_int), bot_set)))),
                               Ty ("prop", [])])])),
             Fv (Var ("x", zero_int), Tv (Var ("'a", zero_int), bot_set))),
        Fv (Var ("x", zero_int), Tv (Var ("'a", zero_int), bot_set)));

val eq_symmetric_ax : term =
  App (App (Ct ("Pure.imp",
                 Ty ("fun",
                      [Ty ("prop", []),
                        Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
             App (App (Ct ("Pure.eq",
                            Ty ("fun",
                                 [the (typ_of
(Fv (Var ("x", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
                                   Ty ("fun",
[the (typ_of (Fv (Var ("y", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
  Ty ("prop", [])])])),
                        Fv (Var ("x", zero_int),
                             Tv (Var ("'a", zero_int), bot_set))),
                   Fv (Var ("y", zero_int),
                        Tv (Var ("'a", zero_int), bot_set)))),
        App (App (Ct ("Pure.eq",
                       Ty ("fun",
                            [the (typ_of
                                   (Fv (Var ("y", zero_int),
 Tv (Var ("'a", zero_int), bot_set)))),
                              Ty ("fun",
                                   [the (typ_of
  (Fv (Var ("x", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
                                     Ty ("prop", [])])])),
                   Fv (Var ("y", zero_int),
                        Tv (Var ("'a", zero_int), bot_set))),
              Fv (Var ("x", zero_int), Tv (Var ("'a", zero_int), bot_set))));

fun product (Set xs) (Set ys) = Set (maps (fn x => map (fn a => (x, a)) ys) xs);

fun exe_antisym A_ [] = true
  | exe_antisym A_ ((x, y) :: r) =
    (if membera (equal_prod A_ A_) r (y, x) then eq A_ x y else true) andalso
      exe_antisym A_ r;

val top_set : 'a set = Coset [];

fun exe_wf_subclass A_ cs =
  less_eq_set (equal_prod A_ A_) (Set cs)
    (product (field A_ (Set cs)) (field A_ (Set cs))) andalso
    (trans_on A_ top_set (Set cs) andalso
      (exe_antisym A_ cs andalso refl_on A_ (field A_ (Set cs)) (Set cs)));

fun exe_class_conds cs = distinct (equal_prod equal_literal equal_literal) cs;

fun exe_ars_condsa (A1_, A2_) (B1_, B2_) arss =
  distinct A1_ (map fst arss) andalso
    ball (image snd (Set arss)) (fn ars => distinct B1_ (map fst ars));

fun exe_ars_conds arss =
  exe_ars_condsa (equal_literal, linorder_literal)
    (equal_literal, linorder_literal) arss;

fun exe_osig_conds a = exe_class_conds (fst a) andalso exe_ars_conds (snd a);

fun exe_all_normalized_and_ex_tcsigs cs arss =
  ball (image snd (Set arss))
    (fn ars => ball (image snd (Set ars)) (list_all (exewf_sort cs)));

fun exe_consistent_length_tcsigs arss =
  ball (image snd (Set arss))
    (fn ars =>
      ball (image snd (Set ars))
        (fn ss_1 =>
          ball (image snd (Set ars))
            (fn ss_2 => equal_nata (size_list ss_1) (size_list ss_2))));

fun exe_coregular_tcsigs cs arss =
  ball (image snd (Set arss))
    (fn ars =>
      ball (image fst (Set ars))
        (fn c_1 =>
          ball (image fst (Set ars))
            (fn c_2 =>
              (if class_leq equal_literal equal_literal (Set cs) c_1 c_2
                then list_all2 (sort_leq equal_literal equal_literal (Set cs))
                       (the (lookup (fn x => ((x : string) = c_1)) ars))
                       (the (lookup (fn x => ((x : string) = c_2)) ars))
                else true))));

fun exe_complete_tcsigs A_ cs arss =
  ball (image snd (Set arss))
    (fn ars =>
      list_all
        (fn (c_1, c_2) =>
          (if member A_ c_1 (image fst (Set ars))
            then member A_ c_2 (image fst (Set ars)) else true))
        cs);

fun exe_wf_tcsigs cs arss =
  exe_coregular_tcsigs cs arss andalso
    (exe_complete_tcsigs equal_literal cs arss andalso
      (exe_consistent_length_tcsigs arss andalso
        exe_all_normalized_and_ex_tcsigs cs arss));

fun exe_wf_osig oss =
  exe_wf_subclass equal_literal (fst oss) andalso
    (exe_wf_tcsigs (fst oss) (snd oss) andalso exe_osig_conds oss);

fun exe_wf_siga (ExeSignature (cto, tao, sa)) =
  exe_wf_osig sa andalso
    (equal_seta equal_literal (image fst (Set (snd sa)))
       (image fst (Set tao)) andalso
      (ball (image fst (Set (snd sa)))
         (fn typea =>
           ball (image snd
                  (Set (the (lookup (fn k => ((k : string) = typea))
                              (snd sa)))))
             (fn ars =>
               equal_nata (the (lookup (fn k => ((k : string) = typea)) tao))
                 (size_list ars))) andalso
        ball (image snd (Set cto))
          (exetyp_ok_sig (ExeSignature (cto, tao, sa)))));

fun exe_wf_sig sigma = exe_wf_siga sigma;

val eq_transitive_ax : term =
  App (App (Ct ("Pure.imp",
                 Ty ("fun",
                      [Ty ("prop", []),
                        Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
             App (App (Ct ("Pure.eq",
                            Ty ("fun",
                                 [the (typ_of
(Fv (Var ("x", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
                                   Ty ("fun",
[the (typ_of (Fv (Var ("y", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
  Ty ("prop", [])])])),
                        Fv (Var ("x", zero_int),
                             Tv (Var ("'a", zero_int), bot_set))),
                   Fv (Var ("y", zero_int),
                        Tv (Var ("'a", zero_int), bot_set)))),
        App (App (Ct ("Pure.imp",
                       Ty ("fun",
                            [Ty ("prop", []),
                              Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
                   App (App (Ct ("Pure.eq",
                                  Ty ("fun",
                                       [the
  (typ_of (Fv (Var ("y", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
 Ty ("fun",
      [the (typ_of
             (Fv (Var ("z", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
        Ty ("prop", [])])])),
                              Fv (Var ("y", zero_int),
                                   Tv (Var ("'a", zero_int), bot_set))),
                         Fv (Var ("z", zero_int),
                              Tv (Var ("'a", zero_int), bot_set)))),
              App (App (Ct ("Pure.eq",
                             Ty ("fun",
                                  [the (typ_of
 (Fv (Var ("x", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
                                    Ty ("fun",
 [the (typ_of (Fv (Var ("z", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
   Ty ("prop", [])])])),
                         Fv (Var ("x", zero_int),
                              Tv (Var ("'a", zero_int), bot_set))),
                    Fv (Var ("z", zero_int),
                         Tv (Var ("'a", zero_int), bot_set)))));

val eq_combination_ax : term =
  App (App (Ct ("Pure.imp",
                 Ty ("fun",
                      [Ty ("prop", []),
                        Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
             App (App (Ct ("Pure.eq",
                            Ty ("fun",
                                 [the (typ_of
(Fv (Var ("f", zero_int),
      Ty ("fun",
           [Tv (Var ("'a", zero_int), bot_set),
             Tv (Var ("'b", zero_int), bot_set)])))),
                                   Ty ("fun",
[the (typ_of
       (Fv (Var ("g", zero_int),
             Ty ("fun",
                  [Tv (Var ("'a", zero_int), bot_set),
                    Tv (Var ("'b", zero_int), bot_set)])))),
  Ty ("prop", [])])])),
                        Fv (Var ("f", zero_int),
                             Ty ("fun",
                                  [Tv (Var ("'a", zero_int), bot_set),
                                    Tv (Var ("'b", zero_int), bot_set)]))),
                   Fv (Var ("g", zero_int),
                        Ty ("fun",
                             [Tv (Var ("'a", zero_int), bot_set),
                               Tv (Var ("'b", zero_int), bot_set)])))),
        App (App (Ct ("Pure.imp",
                       Ty ("fun",
                            [Ty ("prop", []),
                              Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
                   App (App (Ct ("Pure.eq",
                                  Ty ("fun",
                                       [the
  (typ_of (Fv (Var ("x", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
 Ty ("fun",
      [the (typ_of
             (Fv (Var ("y", zero_int), Tv (Var ("'a", zero_int), bot_set)))),
        Ty ("prop", [])])])),
                              Fv (Var ("x", zero_int),
                                   Tv (Var ("'a", zero_int), bot_set))),
                         Fv (Var ("y", zero_int),
                              Tv (Var ("'a", zero_int), bot_set)))),
              App (App (Ct ("Pure.eq",
                             Ty ("fun",
                                  [the (typ_of
 (App (Fv (Var ("f", zero_int),
            Ty ("fun",
                 [Tv (Var ("'a", zero_int), bot_set),
                   Tv (Var ("'b", zero_int), bot_set)])),
        Fv (Var ("x", zero_int), Tv (Var ("'a", zero_int), bot_set))))),
                                    Ty ("fun",
 [the (typ_of
        (App (Fv (Var ("g", zero_int),
                   Ty ("fun",
                        [Tv (Var ("'a", zero_int), bot_set),
                          Tv (Var ("'b", zero_int), bot_set)])),
               Fv (Var ("y", zero_int), Tv (Var ("'a", zero_int), bot_set))))),
   Ty ("prop", [])])])),
                         App (Fv (Var ("f", zero_int),
                                   Ty ("fun",
[Tv (Var ("'a", zero_int), bot_set), Tv (Var ("'b", zero_int), bot_set)])),
                               Fv (Var ("x", zero_int),
                                    Tv (Var ("'a", zero_int), bot_set)))),
                    App (Fv (Var ("g", zero_int),
                              Ty ("fun",
                                   [Tv (Var ("'a", zero_int), bot_set),
                                     Tv (Var ("'b", zero_int), bot_set)])),
                          Fv (Var ("y", zero_int),
                               Tv (Var ("'a", zero_int), bot_set))))));

fun exe_sig_conds sigma =
  distinct equal_literal (map fst (execonst_type_of sigma)) andalso
    (distinct equal_literal (map fst (exetyp_arity_of sigma)) andalso
      exe_osig_conds (exesorts sigma));

val eq_abstract_rule_ax : term =
  App (App (Ct ("Pure.imp",
                 Ty ("fun",
                      [Ty ("prop", []),
                        Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
             App (Ct ("Pure.all",
                       Ty ("fun",
                            [Ty ("fun",
                                  [Tv (Var ("'a", zero_int), bot_set),
                                    Ty ("prop", [])]),
                              Ty ("prop", [])])),
                   Abs (Tv (Var ("'a", zero_int), bot_set),
                         App (App (Ct ("Pure.eq",
Ty ("fun",
     [Tv (Var ("'b", zero_int), bot_set),
       Ty ("fun", [Tv (Var ("'b", zero_int), bot_set), Ty ("prop", [])])])),
                                    App (Fv
   (Var ("f", zero_int),
     Ty ("fun",
          [Tv (Var ("'a", zero_int), bot_set),
            Tv (Var ("'b", zero_int), bot_set)])),
  Bv zero_nat)),
                               App (Fv (Var ("g", zero_int),
 Ty ("fun",
      [Tv (Var ("'a", zero_int), bot_set),
        Tv (Var ("'b", zero_int), bot_set)])),
                                     Bv zero_nat))))),
        App (App (Ct ("Pure.eq",
                       Ty ("fun",
                            [the (typ_of
                                   (Abs (Tv (Var ("'a", zero_int), bot_set),
  App (Fv (Var ("f", zero_int),
            Ty ("fun",
                 [Tv (Var ("'a", zero_int), bot_set),
                   Tv (Var ("'b", zero_int), bot_set)])),
        Bv zero_nat)))),
                              Ty ("fun",
                                   [the (typ_of
  (Abs (Tv (Var ("'a", zero_int), bot_set),
         App (Fv (Var ("g", zero_int),
                   Ty ("fun",
                        [Tv (Var ("'a", zero_int), bot_set),
                          Tv (Var ("'b", zero_int), bot_set)])),
               Bv zero_nat)))),
                                     Ty ("prop", [])])])),
                   Abs (Tv (Var ("'a", zero_int), bot_set),
                         App (Fv (Var ("f", zero_int),
                                   Ty ("fun",
[Tv (Var ("'a", zero_int), bot_set), Tv (Var ("'b", zero_int), bot_set)])),
                               Bv zero_nat))),
              Abs (Tv (Var ("'a", zero_int), bot_set),
                    App (Fv (Var ("g", zero_int),
                              Ty ("fun",
                                   [Tv (Var ("'a", zero_int), bot_set),
                                     Tv (Var ("'b", zero_int), bot_set)])),
                          Bv zero_nat))));

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun exeis_std_sig (ExeSignature (cto, tao, sorts)) =
  equal_option equal_nat (lookup (fn k => ((k : string) = "fun")) tao)
    (SOME (nat_of_integer (2 : IntInf.int))) andalso
    (equal_option equal_nat (lookup (fn k => ((k : string) = "prop")) tao)
       (SOME zero_nat) andalso
      (equal_option equal_nat (lookup (fn k => ((k : string) = "itself")) tao)
         (SOME one_nat) andalso
        (equal_option equal_typ
           (lookup (fn k => ((k : string) = "Pure.eq")) cto)
           (SOME (Ty ("fun",
                       [Tv (Var ("'a", zero_int), bot_set),
                         Ty ("fun",
                              [Tv (Var ("'a", zero_int), bot_set),
                                Ty ("prop", [])])]))) andalso
          (equal_option equal_typ
             (lookup (fn k => ((k : string) = "Pure.all")) cto)
             (SOME (Ty ("fun",
                         [Ty ("fun",
                               [Tv (Var ("'a", zero_int), bot_set),
                                 Ty ("prop", [])]),
                           Ty ("prop", [])]))) andalso
            (equal_option equal_typ
               (lookup (fn k => ((k : string) = "Pure.imp")) cto)
               (SOME (Ty ("fun",
                           [Ty ("prop", []),
                             Ty ("fun",
                                  [Ty ("prop", []),
                                    Ty ("prop", [])])]))) andalso
              equal_option equal_typ
                (lookup (fn k => ((k : string) = "Pure.type")) cto)
                (SOME (Ty ("itself",
                            [Tv (Var ("'a", zero_int), bot_set)]))))))));

fun exe_wf_theorya (ExeTheory (ExeSignature (cto, tao, sa), ax)) =
  exe_sig_conds (ExeSignature (cto, tao, sa)) andalso
    (list_all
       (fn p =>
         exeterm_oka (ExeSignature (cto, tao, sa)) p andalso
           equal_option equal_typ (typ_of p) (SOME (Ty ("prop", []))))
       ax andalso
      (exeis_std_sig (ExeSignature (cto, tao, sa)) andalso
        (exe_wf_sig (ExeSignature (cto, tao, sa)) andalso
          less_eq_set equal_term
            (insert equal_term eq_reflexive_ax
              (insert equal_term eq_symmetric_ax
                (insert equal_term eq_transitive_ax
                  (insert equal_term eq_intr_ax
                    (insert equal_term eq_elim_ax
                      (insert equal_term eq_combination_ax
                        (insert equal_term eq_abstract_rule_ax bot_set)))))))
            (Set ax))));

fun exe_wf_theory theta = exe_wf_theorya theta;

fun exe_check_proof e p res =
  exe_wf_theorya e andalso equal_option equal_term (exereplay e p) (SOME res);

fun int n = Int_of_integer n;

fun nat n = nat_of_integer n;

fun norm t = map_option eta_norm (beta_norm t);

fun sort xs = Set xs;

fun vars t = rev (add_vars t []);

fun eq_typ a b = equal_typa a b;

fun eq_var a b = equal_variablea a b;

fun eq_term a b = equal_terma a b;

fun term_ok s t = exeterm_oka s t;

fun type_of t = typ_of t;

fun of_class t c = mk_of_class t c;

end; (*struct ExportCheck*)

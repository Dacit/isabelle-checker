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
  val exenormalize_sort : (string * string) list -> string set -> string set
  val exereplay : exetheory -> proofterm -> term option
  val exe_wf_theory : exetheory -> bool
  val exe_check_proof : exetheory -> proofterm -> term -> bool
  val int : IntInf.int -> int
  val nat : IntInf.int -> nat
  val sort : string list -> string set
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

val ord_int = {less_eq = less_eq_int, less = less_int} : int ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : int preorder;

val order_int = {preorder_order = preorder_int} : int order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : int linorder;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun min A_ a b = (if less_eq A_ a b then a else b);

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun inf_nata x = min ord_nat x;

type 'a inf = {inf : 'a -> 'a -> 'a};
val inf = #inf : 'a inf -> 'a -> 'a -> 'a;

val inf_nat = {inf = inf_nata} : nat inf;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun sup_nata x = max ord_nat x;

type 'a sup = {sup : 'a -> 'a -> 'a};
val sup = #sup : 'a sup -> 'a -> 'a -> 'a;

val sup_nat = {sup = sup_nata} : nat sup;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup, order_semilattice_sup : 'a order};
val sup_semilattice_sup = #sup_semilattice_sup : 'a semilattice_sup -> 'a sup;
val order_semilattice_sup = #order_semilattice_sup :
  'a semilattice_sup -> 'a order;

type 'a semilattice_inf =
  {inf_semilattice_inf : 'a inf, order_semilattice_inf : 'a order};
val inf_semilattice_inf = #inf_semilattice_inf : 'a semilattice_inf -> 'a inf;
val order_semilattice_inf = #order_semilattice_inf :
  'a semilattice_inf -> 'a order;

type 'a lattice =
  {semilattice_inf_lattice : 'a semilattice_inf,
    semilattice_sup_lattice : 'a semilattice_sup};
val semilattice_inf_lattice = #semilattice_inf_lattice :
  'a lattice -> 'a semilattice_inf;
val semilattice_sup_lattice = #semilattice_sup_lattice :
  'a lattice -> 'a semilattice_sup;

val semilattice_sup_nat =
  {sup_semilattice_sup = sup_nat, order_semilattice_sup = order_nat} :
  nat semilattice_sup;

val semilattice_inf_nat =
  {inf_semilattice_inf = inf_nat, order_semilattice_inf = order_nat} :
  nat semilattice_inf;

val lattice_nat =
  {semilattice_inf_lattice = semilattice_inf_nat,
    semilattice_sup_lattice = semilattice_sup_nat}
  : nat lattice;

val ceq_nata : (nat -> nat -> bool) option = SOME equal_nata;

type 'a ceq = {ceq : ('a -> 'a -> bool) option};
val ceq = #ceq : 'a ceq -> ('a -> 'a -> bool) option;

val ceq_nat = {ceq = ceq_nata} : nat ceq;

datatype ('a, 'b) phantom = Phantom of 'b;

datatype set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT |
  Set_Monada;

val set_impl_nata : (nat, set_impla) phantom = Phantom Set_RBT;

type 'a set_impl = {set_impl : ('a, set_impla) phantom};
val set_impl = #set_impl : 'a set_impl -> ('a, set_impla) phantom;

val set_impl_nat = {set_impl = set_impl_nata} : nat set_impl;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

datatype ordera = Eq | Lt | Gt;

fun eq A_ a b = equal A_ a b;

fun comparator_of (A1_, A2_) x y =
  (if less ((ord_preorder o preorder_order o order_linorder) A2_) x y then Lt
    else (if eq A1_ x y then Eq else Gt));

fun compare_nat x = comparator_of (equal_nat, linorder_nat) x;

val ccompare_nata : (nat -> nat -> ordera) option = SOME compare_nat;

type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option};
val ccompare = #ccompare : 'a ccompare -> ('a -> 'a -> ordera) option;

val ccompare_nat = {ccompare = ccompare_nata} : nat ccompare;

fun equal_order Lt Gt = false
  | equal_order Gt Lt = false
  | equal_order Eq Gt = false
  | equal_order Gt Eq = false
  | equal_order Eq Lt = false
  | equal_order Lt Eq = false
  | equal_order Gt Gt = true
  | equal_order Lt Lt = true
  | equal_order Eq Eq = true;

datatype ('a, 'b) generator = Generator of (('b -> bool) * ('b -> 'a * 'b));

fun generator (Generator x) = x;

fun fst (x1, x2) = x1;

fun has_next g = fst (generator g);

fun snd (x1, x2) = x2;

fun next g = snd (generator g);

fun sorted_list_subset_fusion less eq g1 g2 s1 s2 =
  (if has_next g1 s1
    then let
           val (x, s1a) = next g1 s1;
         in
           has_next g2 s2 andalso
             let
               val (y, s2a) = next g2 s2;
             in
               (if eq x y then sorted_list_subset_fusion less eq g1 g2 s1a s2a
                 else less y x andalso
                        sorted_list_subset_fusion less eq g1 g2 s1 s2a)
             end
         end
    else true);

fun list_all_fusion g p s =
  (if has_next g s then let
                          val (x, sa) = next g s;
                        in
                          p x andalso list_all_fusion g p sa
                        end
    else true);

datatype color = R | B;

datatype ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;

fun rbt_keys_next ((k, t) :: kts, Empty) = (k, (kts, t))
  | rbt_keys_next (kts, Branch (c, l, k, v, r)) =
    rbt_keys_next ((k, r) :: kts, l);

fun rbt_has_next ([], Empty) = false
  | rbt_has_next (vb :: vc, va) = true
  | rbt_has_next (v, Branch (vb, vc, vd, ve, vf)) = true;

val rbt_keys_generator :
  ('a, (('a * ('a, 'b) rbt) list * ('a, 'b) rbt)) generator
  = Generator (rbt_has_next, rbt_keys_next);

fun lt_of_comp acomp x y =
  (case acomp x y of Eq => false | Lt => true | Gt => false);

datatype ('b, 'a) mapping_rbt = Mapping_RBT of ('b, 'a) rbt;

datatype 'a set_dlist = Abs_dlist of 'a list;

datatype 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
  RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
  Complement of 'a set;

fun list_of_dlist A_ (Abs_dlist x) = x;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun dlist_all A_ x xc = list_all x (list_of_dlist A_ xc);

fun impl_of B_ (Mapping_RBT x) = x;

fun rbt_init x = ([], x);

fun init A_ xa = rbt_init (impl_of A_ xa);

type 'a cenum =
  {cEnum :
     ('a list * ((('a -> bool) -> bool) * (('a -> bool) -> bool))) option};
val cEnum = #cEnum :
  'a cenum ->
    ('a list * ((('a -> bool) -> bool) * (('a -> bool) -> bool))) option;

fun filtera p [] = []
  | filtera p (x :: xs) = (if p x then x :: filtera p xs else filtera p xs);

fun collect A_ p =
  (case cEnum A_ of NONE => Collect_set p
    | SOME (enum, _) => Set_Monad (filtera p enum));

fun list_member equal [] y = false
  | list_member equal (x :: xs) y = equal x y orelse list_member equal xs y;

fun the (SOME x2) = x2;

fun memberc A_ xa = list_member (the (ceq A_)) (list_of_dlist A_ xa);

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun rbt_comp_lookup c Empty k = NONE
  | rbt_comp_lookup c (Branch (uu, l, x, y, r)) k =
    (case c k x of Eq => SOME y | Lt => rbt_comp_lookup c l k
      | Gt => rbt_comp_lookup c r k);

fun lookup A_ xa = rbt_comp_lookup (the (ccompare A_)) (impl_of A_ xa);

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit equal;

fun memberb A_ t x = equal_option equal_unit (lookup A_ t x) (SOME ());

fun member (A1_, A2_) x (Set_Monad xs) =
  (case ceq A1_
    of NONE =>
      (raise Fail "member Set_Monad: ceq = None")
        (fn _ => member (A1_, A2_) x (Set_Monad xs))
    | SOME eq => list_member eq xs x)
  | member (A1_, A2_) xa (Complement x) = not (member (A1_, A2_) xa x)
  | member (A1_, A2_) x (RBT_set rbt) = memberb A2_ rbt x
  | member (A1_, A2_) x (DList_set dxs) = memberc A1_ dxs x
  | member (A1_, A2_) x (Collect_set a) = a x;

fun less_eq_set (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2) =
  (case ccompare A3_
    of NONE =>
      (raise Fail "subset RBT_set RBT_set: ccompare = None")
        (fn _ => less_eq_set (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2))
    | SOME c =>
      (case ceq A2_
        of NONE =>
          sorted_list_subset_fusion (lt_of_comp c)
            (fn x => fn y => equal_order (c x y) Eq) rbt_keys_generator
            rbt_keys_generator (init A3_ rbt1) (init A3_ rbt2)
        | SOME eq =>
          sorted_list_subset_fusion (lt_of_comp c) eq rbt_keys_generator
            rbt_keys_generator (init A3_ rbt1) (init A3_ rbt2)))
  | less_eq_set (A1_, A2_, A3_) (Complement a1) (Complement a2) =
    less_eq_set (A1_, A2_, A3_) a2 a1
  | less_eq_set (A1_, A2_, A3_) (Collect_set p) (Complement a) =
    less_eq_set (A1_, A2_, A3_) a (collect A1_ (fn x => not (p x)))
  | less_eq_set (A1_, A2_, A3_) (RBT_set rbt) b =
    (case ccompare A3_
      of NONE =>
        (raise Fail "subset RBT_set1: ccompare = None")
          (fn _ => less_eq_set (A1_, A2_, A3_) (RBT_set rbt) b)
      | SOME _ =>
        list_all_fusion rbt_keys_generator (fn x => member (A2_, A3_) x b)
          (init A3_ rbt))
  | less_eq_set (A1_, A2_, A3_) (DList_set dxs) c =
    (case ceq A2_
      of NONE =>
        (raise Fail "subset DList_set1: ceq = None")
          (fn _ => less_eq_set (A1_, A2_, A3_) (DList_set dxs) c)
      | SOME _ => dlist_all A2_ (fn x => member (A2_, A3_) x c) dxs)
  | less_eq_set (A1_, A2_, A3_) (Set_Monad xs) c =
    list_all (fn x => member (A2_, A3_) x c) xs;

fun equal_seta (A1_, A2_, A3_, A4_) a b =
  less_eq_set (A1_, A2_, A3_) a b andalso less_eq_set (A1_, A2_, A3_) b a;

fun equal_set (A1_, A2_, A3_, A4_) = {equal = equal_seta (A1_, A2_, A3_, A4_)} :
  'a set equal;

fun uminus_set (Complement b) = b
  | uminus_set (Collect_set p) = Collect_set (fn x => not (p x))
  | uminus_set a = Complement a;

fun balance (Branch (R, a, w, x, b)) s t (Branch (R, c, y, z, d)) =
  Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z Empty =
    Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, a, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z Empty =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance
    (Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c))) y z
    Empty =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance
    (Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance Empty w x (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, d))
  | balance Empty w x (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance Empty w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
  | balance Empty s t Empty = Branch (B, Empty, s, t, Empty)
  | balance Empty s t (Branch (B, va, vb, vc, vd)) =
    Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
  | balance Empty s t (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
  | balance Empty s t (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch
      (B, Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | balance Empty s t (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch
      (B, Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance Empty s t
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, Empty, s, t,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance (Branch (B, va, vb, vc, vd)) s t Empty =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (B, ve, vf, vg, vh)) =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (v, Empty, vf, vg, Empty))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t,
          Branch
            (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (v, Empty, vb, vc, Empty)) s t Empty =
    Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
  | balance (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) s t Empty =
    Branch
      (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty)
  | balance (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) s t Empty =
    Branch
      (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty)
  | balance
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    s t Empty =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty)
  | balance (Branch (v, Empty, vf, vg, Empty)) s t (Branch (B, va, vb, vc, vd))
    = Branch
        (B, Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl))) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty)) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd))
  | balance
    (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)))
    s t (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch
            (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd));

fun rbt_comp_ins c f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_comp_ins c f k v (Branch (B, l, x, y, r)) =
    (case c k x of Eq => Branch (B, l, x, f k y v, r)
      | Lt => balance (rbt_comp_ins c f k v l) x y r
      | Gt => balance l x y (rbt_comp_ins c f k v r))
  | rbt_comp_ins c f k v (Branch (R, l, x, y, r)) =
    (case c k x of Eq => Branch (R, l, x, f k y v, r)
      | Lt => Branch (R, rbt_comp_ins c f k v l, x, y, r)
      | Gt => Branch (R, l, x, y, rbt_comp_ins c f k v r));

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun rbt_comp_insert_with_key c f k v t = paint B (rbt_comp_ins c f k v t);

fun rbt_comp_insert c =
  rbt_comp_insert_with_key c (fn _ => fn _ => fn nv => nv);

fun insertc A_ xc xd xe =
  Mapping_RBT (rbt_comp_insert (the (ccompare A_)) xc xd (impl_of A_ xe));

fun rbt_baliR t1 ab bb (Branch (R, t2, aa, ba, Branch (R, t3, a, b, t4))) =
  Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
  | rbt_baliR t1 ab bb (Branch (R, Branch (R, t2, aa, ba, t3), a, b, Empty)) =
    Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, Empty))
  | rbt_baliR t1 ab bb
    (Branch (R, Branch (R, t2, aa, ba, t3), a, b, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, t1, ab, bb, t2), aa, ba,
        Branch (B, t3, a, b, Branch (B, va, vb, vc, vd)))
  | rbt_baliR t1 a b Empty = Branch (B, t1, a, b, Empty)
  | rbt_baliR t1 a b (Branch (B, va, vb, vc, vd)) =
    Branch (B, t1, a, b, Branch (B, va, vb, vc, vd))
  | rbt_baliR t1 a b (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, t1, a, b, Branch (v, Empty, vb, vc, Empty))
  | rbt_baliR t1 a b (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch (B, t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | rbt_baliR t1 a b (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch (B, t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | rbt_baliR t1 a b
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, t1, a, b,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc,
              Branch (B, vf, vg, vh, vi)));

fun equal_color R B = false
  | equal_color B R = false
  | equal_color B B = true
  | equal_color R R = true;

val zero_nat : nat = Nat (0 : IntInf.int);

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

datatype num = One | Bit0 of num | Bit1 of num;

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun bheight Empty = zero_nat
  | bheight (Branch (c, lt, k, v, rt)) =
    (if equal_color c B then suc (bheight lt) else bheight lt);

fun rbt_joinR l a b r =
  (if less_eq_nat (bheight l) (bheight r) then Branch (R, l, a, b, r)
    else (case l
           of Branch (R, la, ab, ba, ra) =>
             Branch (R, la, ab, ba, rbt_joinR ra a b r)
           | Branch (B, la, ab, ba, ra) =>
             rbt_baliR la ab ba (rbt_joinR ra a b r)));

fun rbt_baliL (Branch (R, Branch (R, t1, ab, bb, t2), aa, ba, t3)) a b t4 =
  Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
  | rbt_baliL (Branch (R, Empty, ab, bb, Branch (R, t2, aa, ba, t3))) a b t4 =
    Branch (R, Branch (B, Empty, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
  | rbt_baliL
    (Branch (R, Branch (B, va, vb, vc, vd), ab, bb, Branch (R, t2, aa, ba, t3)))
    a b t4 =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), ab, bb, t2), aa, ba,
        Branch (B, t3, a, b, t4))
  | rbt_baliL Empty a b t2 = Branch (B, Empty, a, b, t2)
  | rbt_baliL (Branch (B, va, vb, vc, vd)) a b t2 =
    Branch (B, Branch (B, va, vb, vc, vd), a, b, t2)
  | rbt_baliL (Branch (v, Empty, vb, vc, Empty)) a b t2 =
    Branch (B, Branch (v, Empty, vb, vc, Empty), a, b, t2)
  | rbt_baliL (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) a b t2 =
    Branch (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2)
  | rbt_baliL (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) a b t2 =
    Branch (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2)
  | rbt_baliL
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    a b t2 =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        a, b, t2);

fun rbt_joinL l a b r =
  (if less_eq_nat (bheight r) (bheight l) then Branch (R, l, a, b, r)
    else (case r
           of Branch (R, la, ab, ba, ra) =>
             Branch (R, rbt_joinL l a b la, ab, ba, ra)
           | Branch (B, la, ab, ba, ra) =>
             rbt_baliL (rbt_joinL l a b la) ab ba ra));

fun rbt_join l a b r =
  let
    val bhl = bheight l;
    val bhr = bheight r;
  in
    (if less_nat bhr bhl then paint B (rbt_joinR l a b r)
      else (if less_nat bhl bhr then paint B (rbt_joinL l a b r)
             else Branch (B, l, a, b, r)))
  end;

fun rbt_split_comp c Empty k = (Empty, (NONE, Empty))
  | rbt_split_comp c (Branch (uu, l, a, b, r)) x =
    (case c x a of Eq => (l, (SOME b, r))
      | Lt => let
                val (l1, (beta, l2)) = rbt_split_comp c l x;
              in
                (l1, (beta, rbt_join l2 a b r))
              end
      | Gt => let
                val (r1, (beta, r2)) = rbt_split_comp c r x;
              in
                (rbt_join l a b r1, (beta, r2))
              end);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun folda f Empty x = x
  | folda f (Branch (c, lt, k, v, rt)) x = folda f rt (f k v (folda f lt x));

fun rbt_comp_union_swap_rec c f gamma t1 t2 =
  let
    val bh1 = bheight t1;
    val bh2 = bheight t2;
    val (gammaa, (t2a, (bh2a, (t1a, _)))) =
      (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
        else (gamma, (t2, (bh2, (t1, bh1)))));
    val fa = (if gammaa then (fn k => fn v => fn va => f k va v) else f);
  in
    (if less_nat bh2a (nat_of_integer (4 : IntInf.int))
      then folda (rbt_comp_insert_with_key c fa) t2a t1a
      else (case t1a of Empty => t2a
             | Branch (_, l1, a, b, r1) =>
               let
                 val (l2, (beta, r2)) = rbt_split_comp c t2a a;
               in
                 rbt_join (rbt_comp_union_swap_rec c f gammaa l1 l2) a
                   (case beta of NONE => b | SOME ca => fa a b ca)
                   (rbt_comp_union_swap_rec c f gammaa r1 r2)
               end))
  end;

fun rbt_comp_union_with_key c f t1 t2 =
  paint B (rbt_comp_union_swap_rec c f false t1 t2);

fun join A_ xc xd xe =
  Mapping_RBT
    (rbt_comp_union_with_key (the (ccompare A_)) xc (impl_of A_ xd)
      (impl_of A_ xe));

fun list_insert equal x xs = (if list_member equal xs x then xs else x :: xs);

fun insertb A_ xb xc =
  Abs_dlist (list_insert (the (ceq A_)) xb (list_of_dlist A_ xc));

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun foldc A_ x xc = fold x (list_of_dlist A_ xc);

fun uniona A_ = foldc A_ (insertb A_);

fun id x = (fn xa => xa) x;

fun is_none NONE = true
  | is_none (SOME x) = false;

fun inter_list A_ xb xc =
  Mapping_RBT
    (fold (fn k => rbt_comp_insert (the (ccompare A_)) k ())
      (filtera
        (fn x =>
          not (is_none (rbt_comp_lookup (the (ccompare A_)) (impl_of A_ xb) x)))
        xc)
      Empty);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun size_list xs = length_tailrec xs zero_nat;

fun map_prod f g (a, b) = (f a, g b);

fun divmod_nat m n =
  let
    val k = integer_of_nat m;
    val l = integer_of_nat n;
  in
    map_prod nat_of_integer nat_of_integer
      (if ((k : IntInf.int) = (0 : IntInf.int))
        then ((0 : IntInf.int), (0 : IntInf.int))
        else (if ((l : IntInf.int) = (0 : IntInf.int))
               then ((0 : IntInf.int), k)
               else IntInf.divMod (IntInf.abs k, IntInf.abs l)))
  end;

fun apfst f (x, y) = (f x, y);

fun rbtreeify_g n kvs =
  (if equal_nata n zero_nat orelse equal_nata n one_nat then (Empty, kvs)
    else let
           val (na, r) = divmod_nat n (nat_of_integer (2 : IntInf.int));
         in
           (if equal_nata r zero_nat
             then let
                    val (t1, (k, v) :: kvsa) = rbtreeify_g na kvs;
                  in
                    apfst (fn a => Branch (B, t1, k, v, a))
                      (rbtreeify_g na kvsa)
                  end
             else let
                    val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                  in
                    apfst (fn a => Branch (B, t1, k, v, a))
                      (rbtreeify_g na kvsa)
                  end)
         end)
and rbtreeify_f n kvs =
  (if equal_nata n zero_nat then (Empty, kvs)
    else (if equal_nata n one_nat then let
 val (k, v) :: kvsa = kvs;
                                       in
 (Branch (R, Empty, k, v, Empty), kvsa)
                                       end
           else let
                  val (na, r) = divmod_nat n (nat_of_integer (2 : IntInf.int));
                in
                  (if equal_nata r zero_nat
                    then let
                           val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                         in
                           apfst (fn a => Branch (B, t1, k, v, a))
                             (rbtreeify_g na kvsa)
                         end
                    else let
                           val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                         in
                           apfst (fn a => Branch (B, t1, k, v, a))
                             (rbtreeify_f na kvsa)
                         end)
                end));

fun rbtreeify kvs = fst (rbtreeify_g (suc (size_list kvs)) kvs);

fun gen_entries [] Empty = []
  | gen_entries ((kv, t) :: kvts) Empty = kv :: gen_entries kvts t
  | gen_entries kvts (Branch (c, l, k, v, r)) =
    gen_entries (((k, v), r) :: kvts) l;

fun entries x = gen_entries [] x;

fun filterc A_ xb xc =
  Mapping_RBT (rbtreeify (filtera xb (entries (impl_of A_ xc))));

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun map_filter_comp_inter c f t1 t2 =
  map_filter
    (fn (k, v) =>
      (case rbt_comp_lookup c t1 k of NONE => NONE
        | SOME va => SOME (k, f k va v)))
    (entries t2);

fun is_rbt_empty t =
  (case t of Empty => true | Branch (_, _, _, _, _) => false);

fun rbt_split_min Empty = (raise Fail "undefined")
  | rbt_split_min (Branch (uu, l, a, b, r)) =
    (if is_rbt_empty l then (a, (b, r))
      else let
             val (aa, (ba, la)) = rbt_split_min l;
           in
             (aa, (ba, rbt_join la a b r))
           end);

fun rbt_join2 l r =
  (if is_rbt_empty r then l else let
                                   val (a, (b, c)) = rbt_split_min r;
                                 in
                                   rbt_join l a b c
                                 end);

fun rbt_comp_inter_swap_rec c f gamma t1 t2 =
  let
    val bh1 = bheight t1;
    val bh2 = bheight t2;
    val (gammaa, (t2a, (bh2a, (t1a, _)))) =
      (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
        else (gamma, (t2, (bh2, (t1, bh1)))));
    val fa = (if gammaa then (fn k => fn v => fn va => f k va v) else f);
  in
    (if less_nat bh2a (nat_of_integer (4 : IntInf.int))
      then rbtreeify (map_filter_comp_inter c fa t1a t2a)
      else (case t1a of Empty => Empty
             | Branch (_, l1, a, b, r1) =>
               let
                 val (l2, (beta, r2)) = rbt_split_comp c t2a a;
                 val l = rbt_comp_inter_swap_rec c f gammaa l1 l2;
                 val r = rbt_comp_inter_swap_rec c f gammaa r1 r2;
               in
                 (case beta of NONE => rbt_join2 l r
                   | SOME ba => rbt_join l a (fa a b ba) r)
               end))
  end;

fun rbt_comp_inter_with_key c f t1 t2 =
  paint B (rbt_comp_inter_swap_rec c f false t1 t2);

fun meet A_ xc xd xe =
  Mapping_RBT
    (rbt_comp_inter_with_key (the (ccompare A_)) xc (impl_of A_ xd)
      (impl_of A_ xe));

fun filterb A_ xb xc = Abs_dlist (filtera xb (list_of_dlist A_ xc));

fun inf_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad xs) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "inter RBT_set Set_Monad: ccompare = None")
        (fn _ => inf_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad xs))
    | SOME _ => RBT_set (inter_list A2_ rbt1 xs))
  | inf_seta (A1_, A2_) (Set_Monad xs) (RBT_set rbt1) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter Set_Monad RBT_set: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad xs))
      | SOME _ => RBT_set (inter_list A2_ rbt1 xs))
  | inf_seta (A1_, A2_) (Set_Monad xs) (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter Set_Monad DList_set: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (Set_Monad xs) (DList_set dxs2))
      | SOME eq => DList_set (filterb A1_ (list_member eq xs) dxs2))
  | inf_seta (A1_, A2_) (Set_Monad xs1) (Set_Monad xs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter Set_Monad Set_Monad: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (Set_Monad xs1) (Set_Monad xs2))
      | SOME eq => Set_Monad (filtera (list_member eq xs2) xs1))
  | inf_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter RBT_set DList_set: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
      | SOME _ =>
        (case ceq A1_
          of NONE =>
            (raise Fail "inter RBT_set DList_set: ceq = None")
              (fn _ => inf_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
          | SOME _ => RBT_set (inter_list A2_ rbt (list_of_dlist A1_ dxs))))
  | inf_seta (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter RBT_set RBT_set: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2))
      | SOME _ => RBT_set (meet A2_ (fn _ => fn _ => id) rbt1 rbt2))
  | inf_seta (A1_, A2_) (DList_set dxs1) (Set_Monad xs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter DList_set Set_Monad: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (DList_set dxs1) (Set_Monad xs))
      | SOME eq => DList_set (filterb A1_ (list_member eq xs) dxs1))
  | inf_seta (A1_, A2_) (DList_set dxs1) (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter DList_set DList_set: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (DList_set dxs1) (DList_set dxs2))
      | SOME _ => DList_set (filterb A1_ (memberc A1_ dxs2) dxs1))
  | inf_seta (A1_, A2_) (DList_set dxs) (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter DList_set RBT_set: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (DList_set dxs) (RBT_set rbt))
      | SOME _ =>
        (case ceq A1_
          of NONE =>
            (raise Fail "inter DList_set RBT_set: ceq = None")
              (fn _ => inf_seta (A1_, A2_) (DList_set dxs) (RBT_set rbt))
          | SOME _ => RBT_set (inter_list A2_ rbt (list_of_dlist A1_ dxs))))
  | inf_seta (A1_, A2_) (Complement ba) (Complement b) =
    Complement (sup_seta (A1_, A2_) ba b)
  | inf_seta (A1_, A2_) g (RBT_set rbt2) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter RBT_set2: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) g (RBT_set rbt2))
      | SOME _ =>
        RBT_set (filterc A2_ ((fn x => member (A1_, A2_) x g) o fst) rbt2))
  | inf_seta (A1_, A2_) (RBT_set rbt1) g =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter RBT_set1: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (RBT_set rbt1) g)
      | SOME _ =>
        RBT_set (filterc A2_ ((fn x => member (A1_, A2_) x g) o fst) rbt1))
  | inf_seta (A1_, A2_) h (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter DList_set2: ceq = None")
          (fn _ => inf_seta (A1_, A2_) h (DList_set dxs2))
      | SOME _ => DList_set (filterb A1_ (fn x => member (A1_, A2_) x h) dxs2))
  | inf_seta (A1_, A2_) (DList_set dxs1) h =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter DList_set1: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (DList_set dxs1) h)
      | SOME _ => DList_set (filterb A1_ (fn x => member (A1_, A2_) x h) dxs1))
  | inf_seta (A1_, A2_) i (Set_Monad xs) =
    Set_Monad (filtera (fn x => member (A1_, A2_) x i) xs)
  | inf_seta (A1_, A2_) (Set_Monad xs) i =
    Set_Monad (filtera (fn x => member (A1_, A2_) x i) xs)
  | inf_seta (A1_, A2_) j (Collect_set a) =
    Collect_set (fn x => a x andalso member (A1_, A2_) x j)
  | inf_seta (A1_, A2_) (Collect_set a) j =
    Collect_set (fn x => a x andalso member (A1_, A2_) x j)
and sup_seta (A1_, A2_) ba (Complement b) =
  Complement (inf_seta (A1_, A2_) (uminus_set ba) b)
  | sup_seta (A1_, A2_) (Complement ba) b =
    Complement (inf_seta (A1_, A2_) ba (uminus_set b))
  | sup_seta (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union RBT_set RBT_set: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2))
      | SOME _ => RBT_set (join A2_ (fn _ => fn _ => id) rbt1 rbt2))
  | sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union RBT_set DList_set: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
      | SOME _ =>
        (case ceq A1_
          of NONE =>
            (raise Fail "union RBT_set DList_set: ceq = None")
              (fn _ => sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
          | SOME _ => RBT_set (foldc A1_ (fn k => insertc A2_ k ()) dxs rbt)))
  | sup_seta (A1_, A2_) (DList_set dxs) (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union DList_set RBT_set: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
      | SOME _ =>
        (case ceq A1_
          of NONE =>
            (raise Fail "union DList_set RBT_set: ceq = None")
              (fn _ => sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
          | SOME _ => RBT_set (foldc A1_ (fn k => insertc A2_ k ()) dxs rbt)))
  | sup_seta (A1_, A2_) (DList_set dxs1) (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "union DList_set DList_set: ceq = None")
          (fn _ => sup_seta (A1_, A2_) (DList_set dxs1) (DList_set dxs2))
      | SOME _ => DList_set (uniona A1_ dxs1 dxs2))
  | sup_seta (A1_, A2_) (Set_Monad zs) (RBT_set rbt2) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union Set_Monad RBT_set: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (Set_Monad zs) (RBT_set rbt2))
      | SOME _ => RBT_set (fold (fn k => insertc A2_ k ()) zs rbt2))
  | sup_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad zs) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union RBT_set Set_Monad: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad zs))
      | SOME _ => RBT_set (fold (fn k => insertc A2_ k ()) zs rbt1))
  | sup_seta (A1_, A2_) (Set_Monad ws) (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "union Set_Monad DList_set: ceq = None")
          (fn _ => sup_seta (A1_, A2_) (Set_Monad ws) (DList_set dxs2))
      | SOME _ => DList_set (fold (insertb A1_) ws dxs2))
  | sup_seta (A1_, A2_) (DList_set dxs1) (Set_Monad ws) =
    (case ceq A1_
      of NONE =>
        (raise Fail "union DList_set Set_Monad: ceq = None")
          (fn _ => sup_seta (A1_, A2_) (DList_set dxs1) (Set_Monad ws))
      | SOME _ => DList_set (fold (insertb A1_) ws dxs1))
  | sup_seta (A1_, A2_) (Set_Monad xs) (Set_Monad ys) = Set_Monad (xs @ ys)
  | sup_seta (A1_, A2_) b (Collect_set a) =
    Collect_set (fn x => a x orelse member (A1_, A2_) x b)
  | sup_seta (A1_, A2_) (Collect_set a) b =
    Collect_set (fn x => a x orelse member (A1_, A2_) x b);

fun inf_set (A1_, A2_) = {inf = inf_seta (A1_, A2_)} : 'a set inf;

fun sup_set (A1_, A2_) = {sup = sup_seta (A1_, A2_)} : 'a set sup;

fun less_set (A1_, A2_, A3_) a b =
  less_eq_set (A1_, A2_, A3_) a b andalso not (less_eq_set (A1_, A2_, A3_) b a);

fun ord_set (A1_, A2_, A3_) =
  {less_eq = less_eq_set (A1_, A2_, A3_), less = less_set (A1_, A2_, A3_)} :
  'a set ord;

fun preorder_set (A1_, A2_, A3_) = {ord_preorder = ord_set (A1_, A2_, A3_)} :
  'a set preorder;

fun order_set (A1_, A2_, A3_) = {preorder_order = preorder_set (A1_, A2_, A3_)}
  : 'a set order;

fun semilattice_sup_set (A1_, A2_, A3_) =
  {sup_semilattice_sup = sup_set (A2_, A3_),
    order_semilattice_sup = order_set (A1_, A2_, A3_)}
  : 'a set semilattice_sup;

fun semilattice_inf_set (A1_, A2_, A3_) =
  {inf_semilattice_inf = inf_set (A2_, A3_),
    order_semilattice_inf = order_set (A1_, A2_, A3_)}
  : 'a set semilattice_inf;

fun lattice_set (A1_, A2_, A3_) =
  {semilattice_inf_lattice = semilattice_inf_set (A1_, A2_, A3_),
    semilattice_sup_lattice = semilattice_sup_set (A1_, A2_, A3_)}
  : 'a set lattice;

fun list_all2_fusion p g1 g2 s1 s2 =
  (if has_next g1 s1
    then has_next g2 s2 andalso let
                                  val (x, s1a) = next g1 s1;
                                  val (y, s2a) = next g2 s2;
                                in
                                  p x y andalso list_all2_fusion p g1 g2 s1a s2a
                                end
    else not (has_next g2 s2));

fun set_eq (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2) =
  (case ccompare A3_
    of NONE =>
      (raise Fail "set_eq RBT_set RBT_set: ccompare = None")
        (fn _ => set_eq (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2))
    | SOME c =>
      (case ceq A2_
        of NONE =>
          list_all2_fusion (fn x => fn y => equal_order (c x y) Eq)
            rbt_keys_generator rbt_keys_generator (init A3_ rbt1)
            (init A3_ rbt2)
        | SOME eq =>
          list_all2_fusion eq rbt_keys_generator rbt_keys_generator
            (init A3_ rbt1) (init A3_ rbt2)))
  | set_eq (A1_, A2_, A3_) (Complement a) (Complement b) =
    set_eq (A1_, A2_, A3_) a b
  | set_eq (A1_, A2_, A3_) a b =
    less_eq_set (A1_, A2_, A3_) a b andalso less_eq_set (A1_, A2_, A3_) b a;

fun ceq_seta (A1_, A2_, A3_) =
  (case ceq A2_ of NONE => NONE | SOME _ => SOME (set_eq (A1_, A2_, A3_)));

fun ceq_set (A1_, A2_, A3_) = {ceq = ceq_seta (A1_, A2_, A3_)} : 'a set ceq;

val set_impl_seta : ('a set, set_impla) phantom = Phantom Set_Choose;

val set_impl_set = {set_impl = set_impl_seta} : 'a set set_impl;

type 'a finite_UNIV = {finite_UNIV : ('a, bool) phantom};
val finite_UNIV = #finite_UNIV : 'a finite_UNIV -> ('a, bool) phantom;

fun of_phantom (Phantom x) = x;

fun finite_UNIV_seta A_ = Phantom (of_phantom (finite_UNIV A_));

fun finite_UNIV_set A_ = {finite_UNIV = finite_UNIV_seta A_} :
  'a set finite_UNIV;

type 'a cproper_interval =
  {ccompare_cproper_interval : 'a ccompare,
    cproper_interval : 'a option -> 'a option -> bool};
val ccompare_cproper_interval = #ccompare_cproper_interval :
  'a cproper_interval -> 'a ccompare;
val cproper_interval = #cproper_interval :
  'a cproper_interval -> 'a option -> 'a option -> bool;

fun set_less_eq_aux_Compl_fusion less proper_interval g1 g2 ao s1 s2 =
  (if has_next g1 s1
    then (if has_next g2 s2
           then let
                  val (x, s1a) = next g1 s1;
                  val (y, s2a) = next g2 s2;
                in
                  (if less x y
                    then proper_interval ao (SOME x) orelse
                           set_less_eq_aux_Compl_fusion less proper_interval g1
                             g2 (SOME x) s1a s2
                    else (if less y x
                           then proper_interval ao (SOME y) orelse
                                  set_less_eq_aux_Compl_fusion less
                                    proper_interval g1 g2 (SOME y) s1 s2a
                           else proper_interval ao (SOME y)))
                end
           else true)
    else true);

fun compl_set_less_eq_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  (if has_next g1 s1
    then let
           val (x, s1a) = next g1 s1;
         in
           (if has_next g2 s2
             then let
                    val (y, s2a) = next g2 s2;
                  in
                    (if less x y
                      then not (proper_interval ao (SOME x)) andalso
                             compl_set_less_eq_aux_fusion less proper_interval
                               g1 g2 (SOME x) s1a s2
                      else (if less y x
                             then not (proper_interval ao (SOME y)) andalso
                                    compl_set_less_eq_aux_fusion less
                                      proper_interval g1 g2 (SOME y) s1 s2a
                             else not (proper_interval ao (SOME y))))
                  end
             else not (proper_interval ao (SOME x)) andalso
                    compl_set_less_eq_aux_fusion less proper_interval g1 g2
                      (SOME x) s1a s2)
         end
    else (if has_next g2 s2
           then let
                  val (y, s2a) = next g2 s2;
                in
                  not (proper_interval ao (SOME y)) andalso
                    compl_set_less_eq_aux_fusion less proper_interval g1 g2
                      (SOME y) s1 s2a
                end
           else not (proper_interval ao NONE)));

fun set_less_eq_aux_Compl less proper_interval ao [] ys = true
  | set_less_eq_aux_Compl less proper_interval ao xs [] = true
  | set_less_eq_aux_Compl less proper_interval ao (x :: xs) (y :: ys) =
    (if less x y
      then proper_interval ao (SOME x) orelse
             set_less_eq_aux_Compl less proper_interval (SOME x) xs (y :: ys)
      else (if less y x
             then proper_interval ao (SOME y) orelse
                    set_less_eq_aux_Compl less proper_interval (SOME y)
                      (x :: xs) ys
             else proper_interval ao (SOME y)));

fun compl_set_less_eq_aux less proper_interval ao [] [] =
  not (proper_interval ao NONE)
  | compl_set_less_eq_aux less proper_interval ao [] (y :: ys) =
    not (proper_interval ao (SOME y)) andalso
      compl_set_less_eq_aux less proper_interval (SOME y) [] ys
  | compl_set_less_eq_aux less proper_interval ao (x :: xs) [] =
    not (proper_interval ao (SOME x)) andalso
      compl_set_less_eq_aux less proper_interval (SOME x) xs []
  | compl_set_less_eq_aux less proper_interval ao (x :: xs) (y :: ys) =
    (if less x y
      then not (proper_interval ao (SOME x)) andalso
             compl_set_less_eq_aux less proper_interval (SOME x) xs (y :: ys)
      else (if less y x
             then not (proper_interval ao (SOME y)) andalso
                    compl_set_less_eq_aux less proper_interval (SOME y)
                      (x :: xs) ys
             else not (proper_interval ao (SOME y))));

fun lexord_eq_fusion less g1 g2 s1 s2 =
  (if has_next g1 s1
    then has_next g2 s2 andalso
           let
             val (x, s1a) = next g1 s1;
             val (y, s2a) = next g2 s2;
           in
             less x y orelse
               not (less y x) andalso lexord_eq_fusion less g1 g2 s1a s2a
           end
    else true);

fun remdups_sorted less [] = []
  | remdups_sorted less [x] = [x]
  | remdups_sorted less (x :: y :: xs) =
    (if less x y then x :: remdups_sorted less (y :: xs)
      else remdups_sorted less (y :: xs));

fun quicksort_acc less ac [] = ac
  | quicksort_acc less ac [x] = x :: ac
  | quicksort_acc less ac (x :: v :: va) =
    quicksort_part less ac x [] [] [] (v :: va)
and quicksort_part less ac x lts eqs gts [] =
  quicksort_acc less (eqs @ x :: quicksort_acc less ac gts) lts
  | quicksort_part less ac x lts eqs gts (z :: zs) =
    (if less x z then quicksort_part less ac x lts eqs (z :: gts) zs
      else (if less z x then quicksort_part less ac x (z :: lts) eqs gts zs
             else quicksort_part less ac x lts (z :: eqs) gts zs));

fun quicksort less = quicksort_acc less [];

fun gen_keys [] Empty = []
  | gen_keys ((k, t) :: kts) Empty = k :: gen_keys kts t
  | gen_keys kts (Branch (c, l, k, v, r)) = gen_keys ((k, r) :: kts) l;

fun keys x = gen_keys [] x;

fun keysa A_ xa = keys (impl_of A_ xa);

fun csorted_list_of_set (A1_, A2_) (Set_Monad xs) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "csorted_list_of_set Set_Monad: ccompare = None")
        (fn _ => csorted_list_of_set (A1_, A2_) (Set_Monad xs))
    | SOME c => remdups_sorted (lt_of_comp c) (quicksort (lt_of_comp c) xs))
  | csorted_list_of_set (A1_, A2_) (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "csorted_list_of_set DList_set: ceq = None")
          (fn _ => csorted_list_of_set (A1_, A2_) (DList_set dxs))
      | SOME _ =>
        (case ccompare A2_
          of NONE =>
            (raise Fail "csorted_list_of_set DList_set: ccompare = None")
              (fn _ => csorted_list_of_set (A1_, A2_) (DList_set dxs))
          | SOME c => quicksort (lt_of_comp c) (list_of_dlist A1_ dxs)))
  | csorted_list_of_set (A1_, A2_) (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "csorted_list_of_set RBT_set: ccompare = None")
          (fn _ => csorted_list_of_set (A1_, A2_) (RBT_set rbt))
      | SOME _ => keysa A2_ rbt);

fun emptya A_ = Mapping_RBT Empty;

fun empty A_ = Abs_dlist [];

fun set_empty_choose (A1_, A2_) =
  (case ccompare A2_
    of NONE =>
      (case ceq A1_ of NONE => Set_Monad [] | SOME _ => DList_set (empty A1_))
    | SOME _ => RBT_set (emptya A2_));

fun set_empty (A1_, A2_) Set_Collect = Collect_set (fn _ => false)
  | set_empty (A1_, A2_) Set_DList = DList_set (empty A1_)
  | set_empty (A1_, A2_) Set_RBT = RBT_set (emptya A2_)
  | set_empty (A1_, A2_) Set_Monada = Set_Monad []
  | set_empty (A1_, A2_) Set_Choose = set_empty_choose (A1_, A2_);

fun bot_set (A1_, A2_, A3_) = set_empty (A1_, A2_) (of_phantom (set_impl A3_));

fun top_set (A1_, A2_, A3_) = uminus_set (bot_set (A1_, A2_, A3_));

fun le_of_comp acomp x y =
  (case acomp x y of Eq => true | Lt => true | Gt => false);

fun null [] = true
  | null (x :: xs) = false;

fun lexordp_eq less [] ys = true
  | lexordp_eq less xs [] = null xs
  | lexordp_eq less (x :: xs) (y :: ys) =
    less x y orelse not (less y x) andalso lexordp_eq less xs ys;

fun finite (A1_, A2_, A3_) (Collect_set p) =
  of_phantom (finite_UNIV A1_) orelse
    (raise Fail "finite Collect_set")
      (fn _ => finite (A1_, A2_, A3_) (Collect_set p))
  | finite (A1_, A2_, A3_) (Set_Monad xs) = true
  | finite (A1_, A2_, A3_) (Complement a) =
    (if of_phantom (finite_UNIV A1_) then true
      else (if finite (A1_, A2_, A3_) a then false
             else (raise Fail "finite Complement: infinite set")
                    (fn _ => finite (A1_, A2_, A3_) (Complement a))))
  | finite (A1_, A2_, A3_) (RBT_set rbt) =
    (case ccompare A3_
      of NONE =>
        (raise Fail "finite RBT_set: ccompare = None")
          (fn _ => finite (A1_, A2_, A3_) (RBT_set rbt))
      | SOME _ => true)
  | finite (A1_, A2_, A3_) (DList_set dxs) =
    (case ceq A2_
      of NONE =>
        (raise Fail "finite DList_set: ceq = None")
          (fn _ => finite (A1_, A2_, A3_) (DList_set dxs))
      | SOME _ => true);

fun set_less_aux_Compl_fusion less proper_interval g1 g2 ao s1 s2 =
  (if has_next g1 s1
    then let
           val (x, s1a) = next g1 s1;
         in
           (if has_next g2 s2
             then let
                    val (y, s2a) = next g2 s2;
                  in
                    (if less x y
                      then proper_interval ao (SOME x) orelse
                             set_less_aux_Compl_fusion less proper_interval g1
                               g2 (SOME x) s1a s2
                      else (if less y x
                             then proper_interval ao (SOME y) orelse
                                    set_less_aux_Compl_fusion less
                                      proper_interval g1 g2 (SOME y) s1 s2a
                             else proper_interval ao (SOME y)))
                  end
             else proper_interval ao (SOME x) orelse
                    set_less_aux_Compl_fusion less proper_interval g1 g2
                      (SOME x) s1a s2)
         end
    else (if has_next g2 s2
           then let
                  val (y, s2a) = next g2 s2;
                in
                  proper_interval ao (SOME y) orelse
                    set_less_aux_Compl_fusion less proper_interval g1 g2
                      (SOME y) s1 s2a
                end
           else proper_interval ao NONE));

fun compl_set_less_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  has_next g1 s1 andalso
    (has_next g2 s2 andalso
      let
        val (x, s1a) = next g1 s1;
        val (y, s2a) = next g2 s2;
      in
        (if less x y
          then not (proper_interval ao (SOME x)) andalso
                 compl_set_less_aux_fusion less proper_interval g1 g2 (SOME x)
                   s1a s2
          else (if less y x
                 then not (proper_interval ao (SOME y)) andalso
                        compl_set_less_aux_fusion less proper_interval g1 g2
                          (SOME y) s1 s2a
                 else not (proper_interval ao (SOME y))))
      end);

fun set_less_aux_Compl less proper_interval ao [] [] = proper_interval ao NONE
  | set_less_aux_Compl less proper_interval ao [] (y :: ys) =
    proper_interval ao (SOME y) orelse
      set_less_aux_Compl less proper_interval (SOME y) [] ys
  | set_less_aux_Compl less proper_interval ao (x :: xs) [] =
    proper_interval ao (SOME x) orelse
      set_less_aux_Compl less proper_interval (SOME x) xs []
  | set_less_aux_Compl less proper_interval ao (x :: xs) (y :: ys) =
    (if less x y
      then proper_interval ao (SOME x) orelse
             set_less_aux_Compl less proper_interval (SOME x) xs (y :: ys)
      else (if less y x
             then proper_interval ao (SOME y) orelse
                    set_less_aux_Compl less proper_interval (SOME y) (x :: xs)
                      ys
             else proper_interval ao (SOME y)));

fun compl_set_less_aux less proper_interval ao [] ys = false
  | compl_set_less_aux less proper_interval ao xs [] = false
  | compl_set_less_aux less proper_interval ao (x :: xs) (y :: ys) =
    (if less x y
      then not (proper_interval ao (SOME x)) andalso
             compl_set_less_aux less proper_interval (SOME x) xs (y :: ys)
      else (if less y x
             then not (proper_interval ao (SOME y)) andalso
                    compl_set_less_aux less proper_interval (SOME y) (x :: xs)
                      ys
             else not (proper_interval ao (SOME y))));

fun lexord_fusion less g1 g2 s1 s2 =
  (if has_next g1 s1
    then (if has_next g2 s2
           then let
                  val (x, s1a) = next g1 s1;
                  val (y, s2a) = next g2 s2;
                in
                  less x y orelse
                    not (less y x) andalso lexord_fusion less g1 g2 s1a s2a
                end
           else false)
    else has_next g2 s2);

fun lexordp less [] ys = not (null ys)
  | lexordp less xs [] = false
  | lexordp less (x :: xs) (y :: ys) =
    less x y orelse not (less y x) andalso lexordp less xs ys;

fun comp_of_ords le lt x y =
  (if lt x y then Lt else (if le x y then Eq else Gt));

fun ccompare_seta (A1_, A2_, A3_, A4_) =
  (case ccompare (ccompare_cproper_interval A3_) of NONE => NONE
    | SOME _ =>
      SOME (comp_of_ords (cless_eq_set (A1_, A2_, A3_, A4_))
             (cless_set (A1_, A2_, A3_, A4_))))
and cless_set (A1_, A2_, A3_, A4_) (Complement (RBT_set rbt1)) (RBT_set rbt2) =
  (case ccompare (ccompare_cproper_interval A3_)
    of NONE =>
      (raise Fail "cless_set (Complement RBT_set) RBT_set: ccompare = None")
        (fn _ =>
          cless_set (A1_, A2_, A3_, A4_) (Complement (RBT_set rbt1))
            (RBT_set rbt2))
    | SOME c =>
      finite (A1_, A2_, ccompare_cproper_interval A3_)
        (top_set (A2_, ccompare_cproper_interval A3_, A4_)) andalso
        compl_set_less_aux_fusion (lt_of_comp c) (cproper_interval A3_)
          rbt_keys_generator rbt_keys_generator NONE
          (init (ccompare_cproper_interval A3_) rbt1)
          (init (ccompare_cproper_interval A3_) rbt2))
  | cless_set (A1_, A2_, A3_, A4_) (RBT_set rbt1) (Complement (RBT_set rbt2)) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set RBT_set (Complement RBT_set): ccompare = None")
          (fn _ =>
            cless_set (A1_, A2_, A3_, A4_) (RBT_set rbt1)
              (Complement (RBT_set rbt2)))
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_)
              (top_set (A2_, ccompare_cproper_interval A3_, A4_))
          then set_less_aux_Compl_fusion (lt_of_comp c) (cproper_interval A3_)
                 rbt_keys_generator rbt_keys_generator NONE
                 (init (ccompare_cproper_interval A3_) rbt1)
                 (init (ccompare_cproper_interval A3_) rbt2)
          else true))
  | cless_set (A1_, A2_, A3_, A4_) (RBT_set rbta) (RBT_set rbt) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set RBT_set RBT_set: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) (RBT_set rbta) (RBT_set rbt))
      | SOME c =>
        lexord_fusion (fn x => fn y => lt_of_comp c y x) rbt_keys_generator
          rbt_keys_generator (init (ccompare_cproper_interval A3_) rbta)
          (init (ccompare_cproper_interval A3_) rbt))
  | cless_set (A1_, A2_, A3_, A4_) (Complement a) (Complement b) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set Complement Complement: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) (Complement a) (Complement b))
      | SOME _ => lt_of_comp (the (ccompare_seta (A1_, A2_, A3_, A4_))) b a)
  | cless_set (A1_, A2_, A3_, A4_) (Complement a) b =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set Complement1: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) (Complement a) b)
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then finite (A1_, A2_, ccompare_cproper_interval A3_)
                 (top_set (A2_, ccompare_cproper_interval A3_, A4_)) andalso
                 compl_set_less_aux (lt_of_comp c) (cproper_interval A3_) NONE
                   (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) a)
                   (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) b)
          else (raise Fail "cless_set Complement1: infinite set")
                 (fn _ => cless_set (A1_, A2_, A3_, A4_) (Complement a) b)))
  | cless_set (A1_, A2_, A3_, A4_) a (Complement b) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set Complement2: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) a (Complement b))
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then (if finite (A1_, A2_, ccompare_cproper_interval A3_)
                     (top_set (A2_, ccompare_cproper_interval A3_, A4_))
                 then set_less_aux_Compl (lt_of_comp c) (cproper_interval A3_)
                        NONE
                        (csorted_list_of_set
                          (A2_, ccompare_cproper_interval A3_) a)
                        (csorted_list_of_set
                          (A2_, ccompare_cproper_interval A3_) b)
                 else true)
          else (raise Fail "cless_set Complement2: infinite set")
                 (fn _ => cless_set (A1_, A2_, A3_, A4_) a (Complement b))))
  | cless_set (A1_, A2_, A3_, A4_) a b =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) a b)
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then lexordp (fn x => fn y => lt_of_comp c y x)
                 (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) a)
                 (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) b)
          else (raise Fail "cless_set: infinite set")
                 (fn _ => cless_set (A1_, A2_, A3_, A4_) a b)))
and cless_eq_set (A1_, A2_, A3_, A4_) (Complement (RBT_set rbt1)) (RBT_set rbt2)
  = (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail
          "cless_eq_set (Complement RBT_set) RBT_set: ccompare = None")
          (fn _ =>
            cless_eq_set (A1_, A2_, A3_, A4_) (Complement (RBT_set rbt1))
              (RBT_set rbt2))
      | SOME c =>
        finite (A1_, A2_, ccompare_cproper_interval A3_)
          (top_set (A2_, ccompare_cproper_interval A3_, A4_)) andalso
          compl_set_less_eq_aux_fusion (lt_of_comp c) (cproper_interval A3_)
            rbt_keys_generator rbt_keys_generator NONE
            (init (ccompare_cproper_interval A3_) rbt1)
            (init (ccompare_cproper_interval A3_) rbt2))
  | cless_eq_set (A1_, A2_, A3_, A4_) (RBT_set rbt1) (Complement (RBT_set rbt2))
    = (case ccompare (ccompare_cproper_interval A3_)
        of NONE =>
          (raise Fail
            "cless_eq_set RBT_set (Complement RBT_set): ccompare = None")
            (fn _ =>
              cless_eq_set (A1_, A2_, A3_, A4_) (RBT_set rbt1)
                (Complement (RBT_set rbt2)))
        | SOME c =>
          (if finite (A1_, A2_, ccompare_cproper_interval A3_)
                (top_set (A2_, ccompare_cproper_interval A3_, A4_))
            then set_less_eq_aux_Compl_fusion (lt_of_comp c)
                   (cproper_interval A3_) rbt_keys_generator rbt_keys_generator
                   NONE (init (ccompare_cproper_interval A3_) rbt1)
                   (init (ccompare_cproper_interval A3_) rbt2)
            else true))
  | cless_eq_set (A1_, A2_, A3_, A4_) (RBT_set rbta) (RBT_set rbt) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set RBT_set RBT_set: ccompare = None")
          (fn _ =>
            cless_eq_set (A1_, A2_, A3_, A4_) (RBT_set rbta) (RBT_set rbt))
      | SOME c =>
        lexord_eq_fusion (fn x => fn y => lt_of_comp c y x) rbt_keys_generator
          rbt_keys_generator (init (ccompare_cproper_interval A3_) rbta)
          (init (ccompare_cproper_interval A3_) rbt))
  | cless_eq_set (A1_, A2_, A3_, A4_) (Complement a) (Complement b) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set Complement Complement: ccompare = None")
          (fn _ =>
            le_of_comp (the (ccompare_seta (A1_, A2_, A3_, A4_))) (Complement a)
              (Complement b))
      | SOME _ => cless_eq_set (A1_, A2_, A3_, A4_) b a)
  | cless_eq_set (A1_, A2_, A3_, A4_) (Complement a) b =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set Complement1: ccompare = None")
          (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) (Complement a) b)
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then finite (A1_, A2_, ccompare_cproper_interval A3_)
                 (top_set (A2_, ccompare_cproper_interval A3_, A4_)) andalso
                 compl_set_less_eq_aux (lt_of_comp c) (cproper_interval A3_)
                   NONE
                   (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) a)
                   (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) b)
          else (raise Fail "cless_eq_set Complement1: infinite set")
                 (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) (Complement a) b)))
  | cless_eq_set (A1_, A2_, A3_, A4_) a (Complement b) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set Complement2: ccompare = None")
          (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) a (Complement b))
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then (if finite (A1_, A2_, ccompare_cproper_interval A3_)
                     (top_set (A2_, ccompare_cproper_interval A3_, A4_))
                 then set_less_eq_aux_Compl (lt_of_comp c)
                        (cproper_interval A3_) NONE
                        (csorted_list_of_set
                          (A2_, ccompare_cproper_interval A3_) a)
                        (csorted_list_of_set
                          (A2_, ccompare_cproper_interval A3_) b)
                 else true)
          else (raise Fail "cless_eq_set Complement2: infinite set")
                 (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) a (Complement b))))
  | cless_eq_set (A1_, A2_, A3_, A4_) a b =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set: ccompare = None")
          (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) a b)
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then lexordp_eq (fn x => fn y => lt_of_comp c y x)
                 (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) a)
                 (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) b)
          else (raise Fail "cless_eq_set: infinite set")
                 (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) a b)));

fun ccompare_set (A1_, A2_, A3_, A4_) =
  {ccompare = ccompare_seta (A1_, A2_, A3_, A4_)} : 'a set ccompare;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

datatype variable = Free of string | Var of (string * int);

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

fun equal_variablea (Free x1) (Var x2) = false
  | equal_variablea (Var x2) (Free x1) = false
  | equal_variablea (Var x2) (Var y2) =
    equal_proda equal_literal equal_int x2 y2
  | equal_variablea (Free x1) (Free y1) = ((x1 : string) = y1);

fun equal_list A_ [] (x21 :: x22) = false
  | equal_list A_ (x21 :: x22) [] = false
  | equal_list A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_list A_ x22 y22
  | equal_list A_ [] [] = true;

datatype typ = Ty of string * typ list | Tv of variable * string set;

val ord_literal =
  {less_eq = (fn a => fn b => ((a : string) <= b)),
    less = (fn a => fn b => ((a : string) < b))}
  : string ord;

val preorder_literal = {ord_preorder = ord_literal} : string preorder;

val order_literal = {preorder_order = preorder_literal} : string order;

val linorder_literal = {order_linorder = order_literal} : string linorder;

fun compare_literal x = comparator_of (equal_literal, linorder_literal) x;

val ccompare_literala : (string -> string -> ordera) option =
  SOME compare_literal;

val ccompare_literal = {ccompare = ccompare_literala} : string ccompare;

val cEnum_literal :
  (string list *
    (((string -> bool) -> bool) * ((string -> bool) -> bool))) option
  = NONE;

val cenum_literal = {cEnum = cEnum_literal} : string cenum;

val ceq_literala : (string -> string -> bool) option =
  SOME (fn a => fn b => ((a : string) = b));

val ceq_literal = {ceq = ceq_literala} : string ceq;

fun equal_typ () = {equal = equal_typa} : typ equal
and equal_typa (Ty (x11, x12)) (Tv (x21, x22)) = false
  | equal_typa (Tv (x21, x22)) (Ty (x11, x12)) = false
  | equal_typa (Tv (x21, x22)) (Tv (y21, y22)) =
    equal_variablea x21 y21 andalso
      set_eq (cenum_literal, ceq_literal, ccompare_literal) x22 y22
  | equal_typa (Ty (x11, x12)) (Ty (y11, y12)) =
    ((x11 : string) = y11) andalso equal_list (equal_typ ()) x12 y12;
val equal_typ = equal_typ ();

val ceq_typa : (typ -> typ -> bool) option = SOME equal_typa;

val ceq_typ = {ceq = ceq_typa} : typ ceq;

val set_impl_typa : (typ, set_impla) phantom = Phantom Set_Choose;

val set_impl_typ = {set_impl = set_impl_typa} : typ set_impl;

val cEnum_typ :
  (typ list * (((typ -> bool) -> bool) * ((typ -> bool) -> bool))) option
  = NONE;

val cenum_typ = {cEnum = cEnum_typ} : typ cenum;

val finite_UNIV_typa : (typ, bool) phantom = Phantom false;

val finite_UNIV_typ = {finite_UNIV = finite_UNIV_typa} : typ finite_UNIV;

val ccompare_typa : (typ -> typ -> ordera) option = NONE;

val ccompare_typ = {ccompare = ccompare_typa} : typ ccompare;

fun cproper_interval_typa uu uv = false;

val cproper_interval_typ =
  {ccompare_cproper_interval = ccompare_typ,
    cproper_interval = cproper_interval_typa}
  : typ cproper_interval;

fun less_eq_bool false b = true
  | less_eq_bool true b = b;

fun less_bool false b = b
  | less_bool true b = false;

val ord_bool = {less_eq = less_eq_bool, less = less_bool} : bool ord;

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

val ceq_terma : (term -> term -> bool) option = SOME equal_terma;

val ceq_term = {ceq = ceq_terma} : term ceq;

val set_impl_terma : (term, set_impla) phantom = Phantom Set_Choose;

val set_impl_term = {set_impl = set_impl_terma} : term set_impl;

val cEnum_term :
  (term list * (((term -> bool) -> bool) * ((term -> bool) -> bool))) option
  = NONE;

val cenum_term = {cEnum = cEnum_term} : term cenum;

val ccompare_terma : (term -> term -> ordera) option = NONE;

val ccompare_term = {ccompare = ccompare_terma} : term ccompare;

fun equality_list eq_a [] [] = true
  | equality_list eq_a [] (y :: ya) = false
  | equality_list eq_a (x :: xa) [] = false
  | equality_list eq_a (x :: xa) (y :: ya) =
    eq_a x y andalso equality_list eq_a xa ya;

fun ceq_lista A_ =
  (case ceq A_ of NONE => NONE | SOME eq_a => SOME (equality_list eq_a));

fun ceq_list A_ = {ceq = ceq_lista A_} : ('a list) ceq;

val set_impl_lista : (('a list), set_impla) phantom = Phantom Set_Choose;

val set_impl_list = {set_impl = set_impl_lista} : ('a list) set_impl;

val cEnum_list :
  (('a list) list *
    ((('a list -> bool) -> bool) * (('a list -> bool) -> bool))) option
  = NONE;

val cenum_list = {cEnum = cEnum_list} : ('a list) cenum;

fun comparator_list comp_a [] [] = Eq
  | comparator_list comp_a [] (y :: ya) = Lt
  | comparator_list comp_a (x :: xa) [] = Gt
  | comparator_list comp_a (x :: xa) (y :: ya) =
    (case comp_a x y of Eq => comparator_list comp_a xa ya | Lt => Lt
      | Gt => Gt);

fun ccompare_lista A_ =
  (case ccompare A_ of NONE => NONE
    | SOME comp_a => SOME (comparator_list comp_a));

fun ccompare_list A_ = {ccompare = ccompare_lista A_} : ('a list) ccompare;

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

fun lexordp_eqa A_ [] ys = true
  | lexordp_eqa A_ xs [] = null xs
  | lexordp_eqa A_ (x :: xs) (y :: ys) =
    less A_ x y orelse not (less A_ y x) andalso lexordp_eqa A_ xs ys;

fun less_eq_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7))
  (Chara (c0, c1, c2, c3, c4, c5, c6, c7)) =
  lexordp_eqa ord_bool [b7, b6, b5, b4, b3, b2, b1, b0]
    [c7, c6, c5, c4, c3, c2, c1, c0];

fun lexordpa A_ [] ys = not (null ys)
  | lexordpa A_ xs [] = false
  | lexordpa A_ (x :: xs) (y :: ys) =
    less A_ x y orelse not (less A_ y x) andalso lexordpa A_ xs ys;

fun less_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7))
  (Chara (c0, c1, c2, c3, c4, c5, c6, c7)) =
  lexordpa ord_bool [b7, b6, b5, b4, b3, b2, b1, b0]
    [c7, c6, c5, c4, c3, c2, c1, c0];

val ord_char = {less_eq = less_eq_char, less = less_char} : char ord;

val preorder_char = {ord_preorder = ord_char} : char preorder;

val order_char = {preorder_order = preorder_char} : char order;

val ceq_chara : (char -> char -> bool) option = SOME equal_chara;

val ceq_char = {ceq = ceq_chara} : char ceq;

val linorder_char = {order_linorder = order_char} : char linorder;

fun compare_char x = comparator_of (equal_char, linorder_char) x;

val ccompare_chara : (char -> char -> ordera) option = SOME compare_char;

val ccompare_char = {ccompare = ccompare_chara} : char ccompare;

val equal_variable = {equal = equal_variablea} : variable equal;

val ceq_variablea : (variable -> variable -> bool) option =
  SOME equal_variablea;

val ceq_variable = {ceq = ceq_variablea} : variable ceq;

val set_impl_variablea : (variable, set_impla) phantom = Phantom Set_RBT;

val set_impl_variable = {set_impl = set_impl_variablea} : variable set_impl;

val cEnum_variable :
  (variable list *
    (((variable -> bool) -> bool) * ((variable -> bool) -> bool))) option
  = NONE;

val cenum_variable = {cEnum = cEnum_variable} : variable cenum;

val finite_UNIV_variablea : (variable, bool) phantom = Phantom false;

val finite_UNIV_variable = {finite_UNIV = finite_UNIV_variablea} :
  variable finite_UNIV;

fun comparator_prod comp_a comp_b (x, xa) (y, ya) =
  (case comp_a x y of Eq => comp_b xa ya | Lt => Lt | Gt => Gt);

fun comparator_variable (Free x) (Free y) =
  comparator_of (equal_literal, linorder_literal) x y
  | comparator_variable (Free x) (Var ya) = Lt
  | comparator_variable (Var x) (Free y) = Gt
  | comparator_variable (Var x) (Var ya) =
    comparator_prod (comparator_of (equal_literal, linorder_literal))
      (comparator_of (equal_int, linorder_int)) x ya;

val ccompare_variablea : (variable -> variable -> ordera) option =
  SOME comparator_variable;

val ccompare_variable = {ccompare = ccompare_variablea} : variable ccompare;

fun cproper_interval_variablea uu uv = false;

val cproper_interval_variable =
  {ccompare_cproper_interval = ccompare_variable,
    cproper_interval = cproper_interval_variablea}
  : variable cproper_interval;

val set_impl_literala : (string, set_impla) phantom = Phantom Set_RBT;

val set_impl_literal = {set_impl = set_impl_literala} : string set_impl;

val finite_UNIV_literala : (string, bool) phantom = Phantom false;

val finite_UNIV_literal = {finite_UNIV = finite_UNIV_literala} :
  string finite_UNIV;

fun cproper_interval_literala xso yso = (raise Fail "undefined");

val cproper_interval_literal =
  {ccompare_cproper_interval = ccompare_literal,
    cproper_interval = cproper_interval_literala}
  : string cproper_interval;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun equality_prod eq_a eq_b (x, xa) (y, ya) = eq_a x y andalso eq_b xa ya;

fun ceq_proda A_ B_ =
  (case ceq A_ of NONE => NONE
    | SOME eq_a =>
      (case ceq B_ of NONE => NONE
        | SOME eq_b => SOME (equality_prod eq_a eq_b)));

fun ceq_prod A_ B_ = {ceq = ceq_proda A_ B_} : ('a * 'b) ceq;

fun set_impl_choose2 Set_Monada Set_Monada = Set_Monada
  | set_impl_choose2 Set_RBT Set_RBT = Set_RBT
  | set_impl_choose2 Set_DList Set_DList = Set_DList
  | set_impl_choose2 Set_Collect Set_Collect = Set_Collect
  | set_impl_choose2 x y = Set_Choose;

fun set_impl_proda A_ B_ =
  Phantom
    (set_impl_choose2 (of_phantom (set_impl A_)) (of_phantom (set_impl B_)));

fun set_impl_prod A_ B_ = {set_impl = set_impl_proda A_ B_} :
  ('a * 'b) set_impl;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun product [] uu = []
  | product (x :: xs) ys = map (fn a => (x, a)) ys @ product xs ys;

fun cEnum_prod A_ B_ =
  (case cEnum A_ of NONE => NONE
    | SOME (enum_a, (enum_all_a, enum_ex_a)) =>
      (case cEnum B_ of NONE => NONE
        | SOME (enum_b, (enum_all_b, enum_ex_b)) =>
          SOME (product enum_a enum_b,
                 ((fn p => enum_all_a (fn x => enum_all_b (fn y => p (x, y)))),
                   (fn p =>
                     enum_ex_a (fn x => enum_ex_b (fn y => p (x, y))))))));

fun cenum_prod A_ B_ = {cEnum = cEnum_prod A_ B_} : ('a * 'b) cenum;

fun finite_UNIV_proda A_ B_ =
  Phantom (of_phantom (finite_UNIV A_) andalso of_phantom (finite_UNIV B_));

fun finite_UNIV_prod A_ B_ = {finite_UNIV = finite_UNIV_proda A_ B_} :
  ('a * 'b) finite_UNIV;

fun ccompare_proda A_ B_ =
  (case ccompare A_ of NONE => NONE
    | SOME comp_a =>
      (case ccompare B_ of NONE => NONE
        | SOME comp_b => SOME (comparator_prod comp_a comp_b)));

fun ccompare_prod A_ B_ = {ccompare = ccompare_proda A_ B_} :
  ('a * 'b) ccompare;

fun cproper_interval_proda A_ B_ NONE NONE = true
  | cproper_interval_proda A_ B_ NONE (SOME (y1, y2)) =
    cproper_interval A_ NONE (SOME y1) orelse cproper_interval B_ NONE (SOME y2)
  | cproper_interval_proda A_ B_ (SOME (x1, x2)) NONE =
    cproper_interval A_ (SOME x1) NONE orelse cproper_interval B_ (SOME x2) NONE
  | cproper_interval_proda A_ B_ (SOME (x1, x2)) (SOME (y1, y2)) =
    cproper_interval A_ (SOME x1) (SOME y1) orelse
      (lt_of_comp (the (ccompare (ccompare_cproper_interval A_))) x1 y1 andalso
         (cproper_interval B_ (SOME x2) NONE orelse
           cproper_interval B_ NONE (SOME y2)) orelse
        not (lt_of_comp (the (ccompare (ccompare_cproper_interval A_))) y1
              x1) andalso
          cproper_interval B_ (SOME x2) (SOME y2));

fun cproper_interval_prod A_ B_ =
  {ccompare_cproper_interval =
     ccompare_prod (ccompare_cproper_interval A_)
       (ccompare_cproper_interval B_),
    cproper_interval = cproper_interval_proda A_ B_}
  : ('a * 'b) cproper_interval;

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

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

datatype ('b, 'a) comp_fun_idem = Abs_comp_fun_idem of ('b -> 'a -> 'a);

datatype 'a semilattice_set = Abs_semilattice_set of ('a -> 'a -> 'a);

fun comp_fun_idem_apply (Abs_comp_fun_idem x) = x;

fun foldb A_ x xc = folda (fn a => fn _ => x a) (impl_of A_ xc);

fun set_fold_cfi (A1_, A2_) f b (RBT_set rbt) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "set_fold_cfi RBT_set: ccompare = None")
        (fn _ => set_fold_cfi (A1_, A2_) f b (RBT_set rbt))
    | SOME _ => foldb A2_ (comp_fun_idem_apply f) rbt b)
  | set_fold_cfi (A1_, A2_) f b (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "set_fold_cfi DList_set: ceq = None")
          (fn _ => set_fold_cfi (A1_, A2_) f b (DList_set dxs))
      | SOME _ => foldc A1_ (comp_fun_idem_apply f) dxs b)
  | set_fold_cfi (A1_, A2_) f b (Set_Monad xs) =
    fold (comp_fun_idem_apply f) xs b
  | set_fold_cfi (A1_, A2_) f b (Collect_set p) =
    (raise Fail "set_fold_cfi not supported on Collect_set")
      (fn _ => set_fold_cfi (A1_, A2_) f b (Collect_set p))
  | set_fold_cfi (A1_, A2_) f b (Complement a) =
    (raise Fail "set_fold_cfi not supported on Complement")
      (fn _ => set_fold_cfi (A1_, A2_) f b (Complement a));

fun sup_cfi A_ =
  Abs_comp_fun_idem (sup ((sup_semilattice_sup o semilattice_sup_lattice) A_));

fun sup_setb (A1_, A2_, A3_, A4_, A5_) a =
  (if finite
        (finite_UNIV_set A1_, ceq_set (A2_, A3_, ccompare_cproper_interval A4_),
          ccompare_set (A1_, A3_, A4_, A5_))
        a
    then set_fold_cfi
           (ceq_set (A2_, A3_, ccompare_cproper_interval A4_),
             ccompare_set (A1_, A3_, A4_, A5_))
           (sup_cfi (lattice_set (A2_, A3_, ccompare_cproper_interval A4_)))
           (bot_set (A3_, ccompare_cproper_interval A4_, A5_)) a
    else (raise Fail "Sup: infinite")
           (fn _ => sup_setb (A1_, A2_, A3_, A4_, A5_) a));

fun fun_upd equal f aa b a = (if equal aa a then b else f a);

fun balance_right a k x (Branch (R, b, s, y, c)) =
  Branch (R, a, k, x, Branch (B, b, s, y, c))
  | balance_right (Branch (B, a, k, x, b)) s y Empty =
    balance (Branch (R, a, k, x, b)) s y Empty
  | balance_right (Branch (B, a, k, x, b)) s y (Branch (B, va, vb, vc, vd)) =
    balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z Empty =
    Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, balance (paint R a) k x b, s, y,
        Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
  | balance_right Empty k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Empty)) k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh))) k x Empty
    = Empty
  | balance_right Empty k x (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Empty)) k x
    (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl))) k x
    (Branch (B, va, vb, vc, vd)) = Empty;

fun balance_left (Branch (R, a, k, x, b)) s y c =
  Branch (R, Branch (B, a, k, x, b), s, y, c)
  | balance_left Empty k x (Branch (B, a, s, y, b)) =
    balance Empty k x (Branch (R, a, s, y, b))
  | balance_left (Branch (B, va, vb, vc, vd)) k x (Branch (B, a, s, y, b)) =
    balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
  | balance_left Empty k x (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
        balance b t z (paint R c))
  | balance_left Empty k x Empty = Empty
  | balance_left Empty k x (Branch (R, Empty, vb, vc, vd)) = Empty
  | balance_left Empty k x (Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd))
    = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x Empty = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Empty, vf, vg, vh)) = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)) = Empty;

fun combine Empty x = x
  | combine (Branch (v, va, vb, vc, vd)) Empty = Branch (v, va, vb, vc, vd)
  | combine (Branch (R, a, k, x, b)) (Branch (R, c, s, y, d)) =
    (case combine b c
      of Empty => Branch (R, a, k, x, Branch (R, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, a, k, x, b)) (Branch (B, c, s, y, d)) =
    (case combine b c
      of Empty => balance_left a k x (Branch (B, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, va, vb, vc, vd)) (Branch (R, b, k, x, c)) =
    Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
  | combine (Branch (R, a, k, x, b)) (Branch (B, va, vb, vc, vd)) =
    Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));

fun rbt_comp_del c x Empty = Empty
  | rbt_comp_del c x (Branch (uu, a, y, s, b)) =
    (case c x y of Eq => combine a b | Lt => rbt_comp_del_from_left c x a y s b
      | Gt => rbt_comp_del_from_right c x a y s b)
and rbt_comp_del_from_left c x (Branch (B, lt, z, v, rt)) y s b =
  balance_left (rbt_comp_del c x (Branch (B, lt, z, v, rt))) y s b
  | rbt_comp_del_from_left c x Empty y s b =
    Branch (R, rbt_comp_del c x Empty, y, s, b)
  | rbt_comp_del_from_left c x (Branch (R, va, vb, vc, vd)) y s b =
    Branch (R, rbt_comp_del c x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_comp_del_from_right c x a y s (Branch (B, lt, z, v, rt)) =
  balance_right a y s (rbt_comp_del c x (Branch (B, lt, z, v, rt)))
  | rbt_comp_del_from_right c x a y s Empty =
    Branch (R, a, y, s, rbt_comp_del c x Empty)
  | rbt_comp_del_from_right c x a y s (Branch (R, va, vb, vc, vd)) =
    Branch (R, a, y, s, rbt_comp_del c x (Branch (R, va, vb, vc, vd)));

fun rbt_comp_delete c k t = paint B (rbt_comp_del c k t);

fun delete A_ xb xc =
  Mapping_RBT (rbt_comp_delete (the (ccompare A_)) xb (impl_of A_ xc));

fun list_remove1 equal x [] = []
  | list_remove1 equal x (y :: xs) =
    (if equal x y then xs else y :: list_remove1 equal x xs);

fun removea A_ xb xc =
  Abs_dlist (list_remove1 (the (ceq A_)) xb (list_of_dlist A_ xc));

fun insert (A1_, A2_) xa (Complement x) = Complement (remove (A1_, A2_) xa x)
  | insert (A1_, A2_) x (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "insert RBT_set: ccompare = None")
          (fn _ => insert (A1_, A2_) x (RBT_set rbt))
      | SOME _ => RBT_set (insertc A2_ x () rbt))
  | insert (A1_, A2_) x (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "insert DList_set: ceq = None")
          (fn _ => insert (A1_, A2_) x (DList_set dxs))
      | SOME _ => DList_set (insertb A1_ x dxs))
  | insert (A1_, A2_) x (Set_Monad xs) = Set_Monad (x :: xs)
  | insert (A1_, A2_) x (Collect_set a) =
    (case ceq A1_
      of NONE =>
        (raise Fail "insert Collect_set: ceq = None")
          (fn _ => insert (A1_, A2_) x (Collect_set a))
      | SOME eq => Collect_set (fun_upd eq a x true))
and remove (A1_, A2_) x (Complement a) = Complement (insert (A1_, A2_) x a)
  | remove (A1_, A2_) x (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "remove RBT_set: ccompare = None")
          (fn _ => remove (A1_, A2_) x (RBT_set rbt))
      | SOME _ => RBT_set (delete A2_ x rbt))
  | remove (A1_, A2_) x (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "remove DList_set: ceq = None")
          (fn _ => remove (A1_, A2_) x (DList_set dxs))
      | SOME _ => DList_set (removea A1_ x dxs))
  | remove (A1_, A2_) x (Collect_set a) =
    (case ceq A1_
      of NONE =>
        (raise Fail "remove Collect: ceq = None")
          (fn _ => remove (A1_, A2_) x (Collect_set a))
      | SOME eq => Collect_set (fun_upd eq a x false));

fun image (A1_, A2_) (B1_, B2_, B3_) h (RBT_set rbt) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "image RBT_set: ccompare = None")
        (fn _ => image (A1_, A2_) (B1_, B2_, B3_) h (RBT_set rbt))
    | SOME _ => foldb A2_ (insert (B1_, B2_) o h) rbt (bot_set (B1_, B2_, B3_)))
  | image (A1_, A2_) (B1_, B2_, B3_) g (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "image DList_set: ceq = None")
          (fn _ => image (A1_, A2_) (B1_, B2_, B3_) g (DList_set dxs))
      | SOME _ =>
        foldc A1_ (insert (B1_, B2_) o g) dxs (bot_set (B1_, B2_, B3_)))
  | image (A1_, A2_) (B1_, B2_, B3_) f (Complement (Complement b)) =
    image (A1_, A2_) (B1_, B2_, B3_) f b
  | image (A1_, A2_) (B1_, B2_, B3_) f (Collect_set a) =
    (raise Fail "image Collect_set")
      (fn _ => image (A1_, A2_) (B1_, B2_, B3_) f (Collect_set a))
  | image (A1_, A2_) (B1_, B2_, B3_) f (Set_Monad xs) = Set_Monad (map f xs);

fun fva (Ct (uu, uv)) =
  set_empty
    (ceq_prod ceq_variable ceq_typ,
      ccompare_prod ccompare_variable ccompare_typ)
    (of_phantom (set_impl_proda set_impl_variable set_impl_typ))
  | fva (Fv (v, t)) =
    insert
      (ceq_prod ceq_variable ceq_typ,
        ccompare_prod ccompare_variable ccompare_typ)
      (v, t)
      (set_empty
        (ceq_prod ceq_variable ceq_typ,
          ccompare_prod ccompare_variable ccompare_typ)
        (of_phantom (set_impl_proda set_impl_variable set_impl_typ)))
  | fva (Bv uw) =
    set_empty
      (ceq_prod ceq_variable ceq_typ,
        ccompare_prod ccompare_variable ccompare_typ)
      (of_phantom (set_impl_proda set_impl_variable set_impl_typ))
  | fva (Abs (ux, body)) = fva body
  | fva (App (t, u)) =
    sup_seta
      (ceq_prod ceq_variable ceq_typ,
        ccompare_prod ccompare_variable ccompare_typ)
      (fva t) (fva u);

fun fv s =
  sup_setb
    (finite_UNIV_prod finite_UNIV_variable finite_UNIV_typ,
      cenum_prod cenum_variable cenum_typ, ceq_prod ceq_variable ceq_typ,
      cproper_interval_prod cproper_interval_variable cproper_interval_typ,
      set_impl_prod set_impl_variable set_impl_typ)
    (image (ceq_term, ccompare_term)
      (ceq_set
         (cenum_prod cenum_variable cenum_typ, ceq_prod ceq_variable ceq_typ,
           ccompare_cproper_interval
             (cproper_interval_prod cproper_interval_variable
               cproper_interval_typ)),
        ccompare_set
          (finite_UNIV_prod finite_UNIV_variable finite_UNIV_typ,
            ceq_prod ceq_variable ceq_typ,
            cproper_interval_prod cproper_interval_variable
              cproper_interval_typ,
            set_impl_prod set_impl_variable set_impl_typ),
        set_impl_set)
      fva s);

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun dlist_ex A_ x xc = list_ex x (list_of_dlist A_ xc);

fun rBT_Impl_rbt_ex p Empty = false
  | rBT_Impl_rbt_ex p (Branch (c, l, k, v, r)) =
    p k v orelse (rBT_Impl_rbt_ex p l orelse rBT_Impl_rbt_ex p r);

fun ex A_ xb xc = rBT_Impl_rbt_ex xb (impl_of A_ xc);

fun bex (A1_, A2_) (RBT_set rbt) p =
  (case ccompare A2_
    of NONE =>
      (raise Fail "Bex RBT_set: ccompare = None")
        (fn _ => bex (A1_, A2_) (RBT_set rbt) p)
    | SOME _ => ex A2_ (fn k => fn _ => p k) rbt)
  | bex (A1_, A2_) (DList_set dxs) p =
    (case ceq A1_
      of NONE =>
        (raise Fail "Bex DList_set: ceq = None")
          (fn _ => bex (A1_, A2_) (DList_set dxs) p)
      | SOME _ => dlist_ex A1_ p dxs)
  | bex (A1_, A2_) (Set_Monad xs) p = list_ex p xs;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun nth (x :: xs) n =
  (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun zip [] ys = []
  | zip xs [] = []
  | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys;

fun rBT_Impl_rbt_all p Empty = true
  | rBT_Impl_rbt_all p (Branch (c, l, k, v, r)) =
    p k v andalso (rBT_Impl_rbt_all p l andalso rBT_Impl_rbt_all p r);

fun all A_ xb xc = rBT_Impl_rbt_all xb (impl_of A_ xc);

fun ball (A1_, A2_) (RBT_set rbt) p =
  (case ccompare A2_
    of NONE =>
      (raise Fail "Ball RBT_set: ccompare = None")
        (fn _ => ball (A1_, A2_) (RBT_set rbt) p)
    | SOME _ => all A2_ (fn k => fn _ => p k) rbt)
  | ball (A1_, A2_) (DList_set dxs) p =
    (case ceq A1_
      of NONE =>
        (raise Fail "Ball DList_set: ceq = None")
          (fn _ => ball (A1_, A2_) (DList_set dxs) p)
      | SOME _ => dlist_all A1_ p dxs)
  | ball (A1_, A2_) (Set_Monad xs) p = list_all p xs;

fun lift (Bv i) n = (if less_eq_nat n i then Bv (plus_nat i one_nat) else Bv i)
  | lift (Abs (t, body)) n = Abs (t, lift body (plus_nat n one_nat))
  | lift (App (f, t)) n = App (lift f n, lift t n)
  | lift (Ct (v, va)) n = Ct (v, va)
  | lift (Fv (v, va)) n = Fv (v, va);

fun name (Free n) = n
  | name (Var (n, uu)) = n;

fun decr lev (Bv i) =
  (if less_eq_nat lev i then Bv (minus_nat i one_nat) else Bv i)
  | decr lev (Abs (ta, t)) = Abs (ta, decr (plus_nat lev one_nat) t)
  | decr lev (App (t, u)) = App (decr lev t, decr lev u)
  | decr uu (Ct (v, va)) = Ct (v, va)
  | decr uu (Fv (v, va)) = Fv (v, va);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun union A_ = fold (inserta A_);

fun filter (A1_, A2_) p a = inf_seta (A1_, A2_) a (Collect_set p);

fun lookupa uu [] = NONE
  | lookupa f ((x, y) :: xs) = (if f x then SOME y else lookupa f xs);

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun assoc_match (Tv (v, s)) t subs =
  (case lookupa
          (fn x =>
            equal_proda equal_variable
              (equal_set
                (cenum_literal, ceq_literal, ccompare_literal, equal_literal))
              x (v, s))
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

fun hda (x21 :: x22) = x21;

fun hd A_ xa = hda (list_of_dlist A_ xa);

fun tla [] = []
  | tla (x21 :: x22) = x22;

fun tl A_ xa = Abs_dlist (tla (list_of_dlist A_ xa));

fun incr_bv inc n (Bv i) =
  (if less_eq_nat n i then Bv (plus_nat i inc) else Bv i)
  | incr_bv inc n (Abs (t, body)) =
    Abs (t, incr_bv inc (plus_nat n one_nat) body)
  | incr_bv inc n (App (f, t)) = App (incr_bv inc n f, incr_bv inc n t)
  | incr_bv uu uv (Ct (v, va)) = Ct (v, va)
  | incr_bv uu uv (Fv (v, va)) = Fv (v, va);

fun class_leq (A1_, A2_) (B1_, B2_) sub c1 c2 =
  member (ceq_prod A1_ B1_, ccompare_prod A2_ B2_) (c1, c2) sub;

fun sort_leq (A1_, A2_) (B1_, B2_) sub s1 s2 =
  ball (B1_, B2_) s2
    (fn c_2 =>
      bex (A1_, A2_) s1
        (fn c_1 => class_leq (A1_, A2_) (B1_, B2_) sub c_1 c_2));

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

fun set_aux (A1_, A2_) Set_Monada = Set_Monad
  | set_aux (A1_, A2_) Set_Choose =
    (case ccompare A2_
      of NONE =>
        (case ceq A1_ of NONE => Set_Monad
          | SOME _ =>
            foldl (fn s => fn x => insert (A1_, A2_) x s)
              (DList_set (empty A1_)))
      | SOME _ =>
        foldl (fn s => fn x => insert (A1_, A2_) x s) (RBT_set (emptya A2_)))
  | set_aux (A1_, A2_) impl =
    foldl (fn s => fn x => insert (A1_, A2_) x s) (set_empty (A1_, A2_) impl);

fun set (A1_, A2_, A3_) xs = set_aux (A1_, A2_) (of_phantom (set_impl A3_)) xs;

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

fun nulla A_ xa = null (list_of_dlist A_ xa);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

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

fun rBT_Impl_fold1 f Empty = (raise Fail "undefined")
  | rBT_Impl_fold1 f (Branch (c, Empty, k, v, r)) =
    folda (fn ka => fn _ => f ka) r k
  | rBT_Impl_fold1 f (Branch (ca, Branch (c, l, ka, va, ra), k, v, r)) =
    folda (fn kb => fn _ => f kb) r
      (f k (rBT_Impl_fold1 f (Branch (c, l, ka, va, ra))));

fun fold1 A_ x xc = rBT_Impl_fold1 x (impl_of A_ xc);

fun domain (A1_, A2_, A3_) (B1_, B2_) r =
  image (ceq_prod A1_ B1_, ccompare_prod A2_ B2_) (A1_, A2_, A3_) fst r;

fun range (A1_, A2_) (B1_, B2_, B3_) r =
  image (ceq_prod A1_ B1_, ccompare_prod A2_ B2_) (B1_, B2_, B3_) snd r;

fun field (A1_, A2_, A3_) r =
  sup_seta (A1_, A2_) (domain (A1_, A2_, A3_) (A1_, A2_) r)
    (range (A1_, A2_) (A1_, A2_, A3_) r);

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

fun semilattice_set_apply (Abs_semilattice_set x) = x;

fun is_empty A_ xa =
  (case impl_of A_ xa of Empty => true | Branch (_, _, _, _, _) => false);

fun set_fold1 (A1_, A2_, A3_) f (RBT_set rbt) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "set_fold1 RBT_set: ccompare = None")
        (fn _ => set_fold1 (A1_, A2_, A3_) f (RBT_set rbt))
    | SOME _ =>
      (if is_empty A2_ rbt
        then (raise Fail "set_fold1 RBT_set: empty set")
               (fn _ => set_fold1 (A1_, A2_, A3_) f (RBT_set rbt))
        else fold1 A2_ (semilattice_set_apply f) rbt))
  | set_fold1 (A1_, A2_, A3_) f (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "set_fold1 DList_set: ceq = None")
          (fn _ => set_fold1 (A1_, A2_, A3_) f (DList_set dxs))
      | SOME _ =>
        (if nulla A1_ dxs
          then (raise Fail "set_fold1 DList_set: empty set")
                 (fn _ => set_fold1 (A1_, A2_, A3_) f (DList_set dxs))
          else foldc A1_ (semilattice_set_apply f) (tl A1_ dxs) (hd A1_ dxs)))
  | set_fold1 (A1_, A2_, A3_) f (Set_Monad (x :: xs)) =
    fold (semilattice_set_apply f) xs x
  | set_fold1 (A1_, A2_, A3_) f (Collect_set p) =
    (raise Fail "set_fold1: Collect_set")
      (fn _ => set_fold1 (A1_, A2_, A3_) f (Collect_set p))
  | set_fold1 (A1_, A2_, A3_) f (Complement a) =
    (raise Fail "set_fold1: Complement")
      (fn _ => set_fold1 (A1_, A2_, A3_) f (Complement a));

fun max_sls A_ =
  Abs_semilattice_set
    (max ((ord_preorder o preorder_order o order_linorder) A_));

fun maxa (A1_, A2_, A3_, A4_) a = set_fold1 (A1_, A2_, A3_) (max_sls A4_) a;

fun fresh_name s =
  (if set_eq (cenum_list, ceq_list ceq_char, ccompare_list ccompare_char) s
        (set_empty (ceq_list ceq_char, ccompare_list ccompare_char)
          (of_phantom set_impl_lista))
    then [Chara (true, false, false, false, false, true, true, false)]
    else replicate
           (plus_nat
             (maxa (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
               (image (ceq_list ceq_char, ccompare_list ccompare_char)
                 (ceq_nat, ccompare_nat, set_impl_nat) size_list s))
             one_nat)
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

fun fresh_namea s =
  implode
    (fresh_name
      (image (ceq_literal, ccompare_literal)
        (ceq_list ceq_char, ccompare_list ccompare_char, set_impl_list) explode
        s));

fun rbt_product f rbt1 rbt2 =
  rbtreeify
    (rev (folda
           (fn a => fn b =>
             folda (fn c => fn d => (fn e => ((a, c), f a b c d) :: e)) rbt2)
           rbt1 []));

fun productd A_ B_ xc xd xe =
  Mapping_RBT (rbt_product xc (impl_of A_ xd) (impl_of B_ xe));

fun producta A_ B_ rbt1 rbt2 =
  productd A_ B_ (fn _ => fn _ => fn _ => fn _ => ()) rbt1 rbt2;

fun refl_on (A1_, A2_) a r =
  ball (A1_, A2_) a
    (fn x => member (ceq_prod A1_ A1_, ccompare_prod A2_ A2_) (x, x) r);

fun mk_all_list l t =
  fold (fn (n, ta) => fn acc =>
         App (Ct ("Pure.all",
                   Ty ("fun",
                        [Ty ("fun", [ta, Ty ("prop", [])]), Ty ("prop", [])])),
               Abs (ta, bind_fv (n, ta) acc)))
    l t;

fun productb A_ B_ dxs1 dxs2 =
  Abs_dlist
    (foldc A_ (fn a => foldc B_ (fn c => (fn b => (a, c) :: b)) dxs2) dxs1 []);

fun trans_on (A1_, A2_, A3_) a r =
  ball (ceq_prod A1_ A1_, ccompare_prod A2_ A2_) r
    (fn (x, y1) =>
      (if member (A1_, A2_) x a
        then (if member (A1_, A2_) y1 a
               then ball (ceq_prod A1_ A1_, ccompare_prod A2_ A2_) r
                      (fn (y2, z) =>
                        (if eq A3_ y1 y2
                          then (if member (A1_, A2_) z a
                                 then member
(ceq_prod A1_ A1_, ccompare_prod A2_ A2_) (x, z) r
                                 else true)
                          else true))
               else true)
        else true));

fun fv_Proof (PAxm (t, uu)) = fva t
  | fv_Proof (PBound uv) =
    set_empty
      (ceq_prod ceq_variable ceq_typ,
        ccompare_prod ccompare_variable ccompare_typ)
      (of_phantom (set_impl_proda set_impl_variable set_impl_typ))
  | fv_Proof (Abst (uw, p)) = fv_Proof p
  | fv_Proof (AbsP (t, p)) =
    sup_seta
      (ceq_prod ceq_variable ceq_typ,
        ccompare_prod ccompare_variable ccompare_typ)
      (fva t) (fv_Proof p)
  | fv_Proof (Appt (p, t)) =
    sup_seta
      (ceq_prod ceq_variable ceq_typ,
        ccompare_prod ccompare_variable ccompare_typ)
      (fv_Proof p) (fva t)
  | fv_Proof (AppP (p1, p2)) =
    sup_seta
      (ceq_prod ceq_variable ceq_typ,
        ccompare_prod ccompare_variable ccompare_typ)
      (fv_Proof p1) (fv_Proof p2)
  | fv_Proof (OfClass (ux, uy)) =
    set_empty
      (ceq_prod ceq_variable ceq_typ,
        ccompare_prod ccompare_variable ccompare_typ)
      (of_phantom (set_impl_proda set_impl_variable set_impl_typ))
  | fv_Proof (Hyp t) = fva t;

fun list_all2 p [] ys = null ys
  | list_all2 p xs [] = null xs
  | list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys;

fun minus_list_set A_ xs ys = fold (removeAll A_) ys xs;

fun exesort_ex (A1_, A2_, A3_, A4_) cs s =
  less_eq_set (A1_, A2_, A3_) s
    (field (A2_, A3_, A4_)
      (set (ceq_prod A2_ A2_, ccompare_prod A3_ A3_, set_impl_prod A4_ A4_)
        cs));

fun execlass_les A_ cs c1 c2 =
  membera (equal_prod A_ A_) cs (c1, c2) andalso
    not (membera (equal_prod A_ A_) cs (c2, c1));

fun exenormalize_sort cs s =
  filter (ceq_literal, ccompare_literal)
    (fn c =>
      not (bex (ceq_literal, ccompare_literal) s
            (fn ca => execlass_les equal_literal cs ca c)))
    s;

fun exenormalized_sort cs s =
  set_eq (cenum_literal, ceq_literal, ccompare_literal) (exenormalize_sort cs s)
    s;

fun exewf_sort sub s =
  set_eq (cenum_literal, ceq_literal, ccompare_literal) s
    (set_empty (ceq_literal, ccompare_literal)
      (of_phantom set_impl_literala)) orelse
    exenormalized_sort sub s andalso
      exesort_ex
        (cenum_literal, ceq_literal, ccompare_literal, set_impl_literal) sub s;

fun exesig (ExeTheory (x1, x2)) = x1;

fun execonst_type_of (ExeSignature (x1, x2, x3)) = x1;

fun exetyp_arity_of (ExeSignature (x1, x2, x3)) = x2;

fun exesorts (ExeSignature (x1, x2, x3)) = x3;

fun exetyp_ok_sig sigma (Ty (c, ts)) =
  (case lookupa (fn k => ((k : string) = c)) (exetyp_arity_of sigma)
    of NONE => false
    | SOME ar =>
      equal_nata (size_list ts) ar andalso list_all (exetyp_ok_sig sigma) ts)
  | exetyp_ok_sig sigma (Tv (uu, s)) = exewf_sort (fst (exesorts sigma)) s;

fun exeterm_oka sigma (Fv (uu, t)) = exetyp_ok_sig sigma t
  | exeterm_oka sigma (Bv uv) = true
  | exeterm_oka sigma (Ct (s, t)) =
    (case lookupa (fn k => ((k : string) = s)) (execonst_type_of sigma)
      of NONE => false | SOME ty => exetyp_ok_sig sigma t andalso tinstT t ty)
  | exeterm_oka sigma (App (t, u)) =
    exeterm_oka sigma t andalso exeterm_oka sigma u
  | exeterm_oka sigma (Abs (ta, t)) =
    exetyp_ok_sig sigma ta andalso exeterm_oka sigma t;

fun exeterm_ok theta t =
  exeterm_oka (exesig theta) t andalso not (is_none (typ_of t));

fun exeaxioms_of (ExeTheory (x1, x2)) = x2;

fun execlass_leq A_ B_ cs c1 c2 = membera (equal_prod A_ B_) cs (c1, c2);

fun exesort_leq (A1_, A2_, A3_) (B1_, B2_, B3_) sub s1 s2 =
  ball (B1_, B2_) s2
    (fn c_2 => bex (A1_, A2_) s1 (fn c_1 => execlass_leq A3_ B3_ sub c_1 c_2));

fun exehas_sort oss (Tv (uu, sa)) s =
  exesort_leq (ceq_literal, ccompare_literal, equal_literal)
    (ceq_literal, ccompare_literal, equal_literal) (fst oss) sa s
  | exehas_sort oss (Ty (a, ts)) s =
    (case lookupa (fn k => ((k : string) = a)) (snd oss) of NONE => false
      | SOME mgd =>
        ball (ceq_literal, ccompare_literal) s
          (fn c =>
            (case lookupa (fn k => ((k : string) = c)) mgd of NONE => false
              | SOME aa => list_all2 (exehas_sort oss) ts aa)));

fun partial_nth [] uu = NONE
  | partial_nth (x :: xs) n =
    (if equal_nata n zero_nat then SOME x
      else partial_nth xs (minus_nat n one_nat));

fun variant_variable (Free n) s =
  let
    val sa =
      fresh_namea
        (image (ceq_variable, ccompare_variable)
          (ceq_literal, ccompare_literal, set_impl_literal) name s);
  in
    (Free sa, insert (ceq_variable, ccompare_variable) (Free sa) s)
  end
  | variant_variable (Var (n, uu)) s =
    let
      val sa =
        fresh_namea
          (image (ceq_variable, ccompare_variable)
            (ceq_literal, ccompare_literal, set_impl_literal) name s);
    in
      (Var (sa, zero_int),
        insert (ceq_variable, ccompare_variable) (Var (sa, zero_int)) s)
    end;

fun the_default a NONE = a
  | the_default uu (SOME b) = b;

fun subst_typ insts (Ty (a, ts)) = Ty (a, map (subst_typ insts) ts)
  | subst_typ insts (Tv (idn, s)) =
    the_default (Tv (idn, s))
      (lookupa
        (fn x =>
          equal_proda equal_variable
            (equal_set
              (cenum_literal, ceq_literal, ccompare_literal, equal_literal))
            x (idn, s))
        insts);

fun exereplaya thy uu uv hs (PAxm (t, tis)) =
  (if distinct
        (equal_prod equal_variable
          (equal_set
            (cenum_literal, ceq_literal, ccompare_literal, equal_literal)))
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
          (insert (ceq_literal, ccompare_literal) c
            (set_empty (ceq_literal, ccompare_literal)
              (of_phantom set_impl_literala))) andalso
          exetyp_ok_sig (exesig thy) ty
      then (case lookupa
                   (fn k =>
                     ((k : string) = (implode (explode c @ explode "_class"))))
                   (execonst_type_of (exesig thy))
             of NONE => NONE | SOME (Ty (_, [])) => NONE
             | SOME (Ty (_, Ty (_, []) :: _)) => NONE
             | SOME (Ty (_, [Ty (_, [_])])) => NONE
             | SOME (Ty (funa, [Ty (it, [ity]), Ty (prop, [])])) =>
               (if equal_typa ity
                     (Tv (Var ("'a", zero_int),
                           set_empty (ceq_literal, ccompare_literal)
                             (of_phantom set_impl_literala))) andalso
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
                (image
                  (ceq_prod ceq_variable ceq_typ,
                    ccompare_prod ccompare_variable ccompare_typ)
                  (ceq_variable, ccompare_variable, set_impl_variable) fst
                  (sup_seta
                    (ceq_prod ceq_variable ceq_typ,
                      ccompare_prod ccompare_variable ccompare_typ)
                    (fv_Proof p)
                    (fv (set (ceq_term, ccompare_term, set_impl_term)
                          (hyps p)))))
                (hyps p) p)
           (fn t => map_option eta_norm (beta_norm t))
    else NONE);

val eq_reflexive_ax : term =
  App (App (Ct ("Pure.eq",
                 Ty ("fun",
                      [the (typ_of
                             (Fv (Var ("x", zero_int),
                                   Tv (Var ("'a", zero_int),
set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala))))),
                        Ty ("fun",
                             [the (typ_of
                                    (Fv (Var ("x", zero_int),
  Tv (Var ("'a", zero_int),
       set_empty (ceq_literal, ccompare_literal)
         (of_phantom set_impl_literala))))),
                               Ty ("prop", [])])])),
             Fv (Var ("x", zero_int),
                  Tv (Var ("'a", zero_int),
                       set_empty (ceq_literal, ccompare_literal)
                         (of_phantom set_impl_literala)))),
        Fv (Var ("x", zero_int),
             Tv (Var ("'a", zero_int),
                  set_empty (ceq_literal, ccompare_literal)
                    (of_phantom set_impl_literala))));

val eq_symmetric_ax : term =
  App (App (Ct ("Pure.imp",
                 Ty ("fun",
                      [Ty ("prop", []),
                        Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
             App (App (Ct ("Pure.eq",
                            Ty ("fun",
                                 [the (typ_of
(Fv (Var ("x", zero_int),
      Tv (Var ("'a", zero_int),
           set_empty (ceq_literal, ccompare_literal)
             (of_phantom set_impl_literala))))),
                                   Ty ("fun",
[the (typ_of
       (Fv (Var ("y", zero_int),
             Tv (Var ("'a", zero_int),
                  set_empty (ceq_literal, ccompare_literal)
                    (of_phantom set_impl_literala))))),
  Ty ("prop", [])])])),
                        Fv (Var ("x", zero_int),
                             Tv (Var ("'a", zero_int),
                                  set_empty (ceq_literal, ccompare_literal)
                                    (of_phantom set_impl_literala)))),
                   Fv (Var ("y", zero_int),
                        Tv (Var ("'a", zero_int),
                             set_empty (ceq_literal, ccompare_literal)
                               (of_phantom set_impl_literala))))),
        App (App (Ct ("Pure.eq",
                       Ty ("fun",
                            [the (typ_of
                                   (Fv (Var ("y", zero_int),
 Tv (Var ("'a", zero_int),
      set_empty (ceq_literal, ccompare_literal)
        (of_phantom set_impl_literala))))),
                              Ty ("fun",
                                   [the (typ_of
  (Fv (Var ("x", zero_int),
        Tv (Var ("'a", zero_int),
             set_empty (ceq_literal, ccompare_literal)
               (of_phantom set_impl_literala))))),
                                     Ty ("prop", [])])])),
                   Fv (Var ("y", zero_int),
                        Tv (Var ("'a", zero_int),
                             set_empty (ceq_literal, ccompare_literal)
                               (of_phantom set_impl_literala)))),
              Fv (Var ("x", zero_int),
                   Tv (Var ("'a", zero_int),
                        set_empty (ceq_literal, ccompare_literal)
                          (of_phantom set_impl_literala)))));

fun productc (A1_, A2_, A3_) (B1_, B2_, B3_) (RBT_set rbt1) (RBT_set rbt2) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "product RBT_set RBT_set: ccompare1 = None")
        (fn _ =>
          productc (A1_, A2_, A3_) (B1_, B2_, B3_) (RBT_set rbt1)
            (RBT_set rbt2))
    | SOME _ =>
      (case ccompare B2_
        of NONE =>
          (raise Fail "product RBT_set RBT_set: ccompare2 = None")
            (fn _ =>
              productc (A1_, A2_, A3_) (B1_, B2_, B3_) (RBT_set rbt1)
                (RBT_set rbt2))
        | SOME _ => RBT_set (producta A2_ B2_ rbt1 rbt2)))
  | productc (A1_, A2_, A3_) (B1_, B2_, B3_) a2 (RBT_set rbt2) =
    (case ccompare B2_
      of NONE =>
        (raise Fail "product RBT_set: ccompare2 = None")
          (fn _ => productc (A1_, A2_, A3_) (B1_, B2_, B3_) a2 (RBT_set rbt2))
      | SOME _ =>
        foldb B2_
          (fn y =>
            sup_seta (ceq_prod A1_ B1_, ccompare_prod A2_ B2_)
              (image (A1_, A2_)
                (ceq_prod A1_ B1_, ccompare_prod A2_ B2_, set_impl_prod A3_ B3_)
                (fn x => (x, y)) a2))
          rbt2
          (bot_set
            (ceq_prod A1_ B1_, ccompare_prod A2_ B2_, set_impl_prod A3_ B3_)))
  | productc (A1_, A2_, A3_) (B1_, B2_, B3_) (RBT_set rbt1) b2 =
    (case ccompare A2_
      of NONE =>
        (raise Fail "product RBT_set: ccompare1 = None")
          (fn _ => productc (A1_, A2_, A3_) (B1_, B2_, B3_) (RBT_set rbt1) b2)
      | SOME _ =>
        foldb A2_
          (fn x =>
            sup_seta (ceq_prod A1_ B1_, ccompare_prod A2_ B2_)
              (image (B1_, B2_)
                (ceq_prod A1_ B1_, ccompare_prod A2_ B2_, set_impl_prod A3_ B3_)
                (fn a => (x, a)) b2))
          rbt1
          (bot_set
            (ceq_prod A1_ B1_, ccompare_prod A2_ B2_, set_impl_prod A3_ B3_)))
  | productc (A1_, A2_, A3_) (B1_, B2_, B3_) (DList_set dxs) (DList_set dys) =
    (case ceq A1_
      of NONE =>
        (raise Fail "product DList_set DList_set: ceq1 = None")
          (fn _ =>
            productc (A1_, A2_, A3_) (B1_, B2_, B3_) (DList_set dxs)
              (DList_set dys))
      | SOME _ =>
        (case ceq B1_
          of NONE =>
            (raise Fail "product DList_set DList_set: ceq2 = None")
              (fn _ =>
                productc (A1_, A2_, A3_) (B1_, B2_, B3_) (DList_set dxs)
                  (DList_set dys))
          | SOME _ => DList_set (productb A1_ B1_ dxs dys)))
  | productc (A1_, A2_, A3_) (B1_, B2_, B3_) a1 (DList_set dys) =
    (case ceq B1_
      of NONE =>
        (raise Fail "product DList_set2: ceq = None")
          (fn _ => productc (A1_, A2_, A3_) (B1_, B2_, B3_) a1 (DList_set dys))
      | SOME _ =>
        foldc B1_
          (fn y =>
            sup_seta (ceq_prod A1_ B1_, ccompare_prod A2_ B2_)
              (image (A1_, A2_)
                (ceq_prod A1_ B1_, ccompare_prod A2_ B2_, set_impl_prod A3_ B3_)
                (fn x => (x, y)) a1))
          dys (bot_set
                (ceq_prod A1_ B1_, ccompare_prod A2_ B2_,
                  set_impl_prod A3_ B3_)))
  | productc (A1_, A2_, A3_) (B1_, B2_, B3_) (DList_set dxs) b1 =
    (case ceq A1_
      of NONE =>
        (raise Fail "product DList_set1: ceq = None")
          (fn _ => productc (A1_, A2_, A3_) (B1_, B2_, B3_) (DList_set dxs) b1)
      | SOME _ =>
        foldc A1_
          (fn x =>
            sup_seta (ceq_prod A1_ B1_, ccompare_prod A2_ B2_)
              (image (B1_, B2_)
                (ceq_prod A1_ B1_, ccompare_prod A2_ B2_, set_impl_prod A3_ B3_)
                (fn a => (x, a)) b1))
          dxs (bot_set
                (ceq_prod A1_ B1_, ccompare_prod A2_ B2_,
                  set_impl_prod A3_ B3_)))
  | productc (A1_, A2_, A3_) (B1_, B2_, B3_) (Set_Monad xs) (Set_Monad ys) =
    Set_Monad (fold (fn x => fold (fn y => (fn a => (x, y) :: a)) ys) xs [])
  | productc (A1_, A2_, A3_) (B1_, B2_, B3_) a b =
    Collect_set
      (fn (x, y) => member (A1_, A2_) x a andalso member (B1_, B2_) y b);

fun exe_antisym A_ [] = true
  | exe_antisym A_ ((x, y) :: r) =
    (if membera (equal_prod A_ A_) r (y, x) then eq A_ x y else true) andalso
      exe_antisym A_ r;

fun exe_wf_subclass (A1_, A2_, A3_, A4_, A5_) cs =
  less_eq_set (cenum_prod A1_ A1_, ceq_prod A2_ A2_, ccompare_prod A3_ A3_)
    (set (ceq_prod A2_ A2_, ccompare_prod A3_ A3_, set_impl_prod A5_ A5_) cs)
    (productc (A2_, A3_, A5_) (A2_, A3_, A5_)
      (field (A2_, A3_, A5_)
        (set (ceq_prod A2_ A2_, ccompare_prod A3_ A3_, set_impl_prod A5_ A5_)
          cs))
      (field (A2_, A3_, A5_)
        (set (ceq_prod A2_ A2_, ccompare_prod A3_ A3_, set_impl_prod A5_ A5_)
          cs))) andalso
    (trans_on (A2_, A3_, A4_) (top_set (A2_, A3_, A5_))
       (set (ceq_prod A2_ A2_, ccompare_prod A3_ A3_, set_impl_prod A5_ A5_)
         cs) andalso
      (exe_antisym A4_ cs andalso
        refl_on (A2_, A3_)
          (field (A2_, A3_, A5_)
            (set (ceq_prod A2_ A2_, ccompare_prod A3_ A3_,
                   set_impl_prod A5_ A5_)
              cs))
          (set (ceq_prod A2_ A2_, ccompare_prod A3_ A3_, set_impl_prod A5_ A5_)
            cs)));

fun exe_class_conds cs = distinct (equal_prod equal_literal equal_literal) cs;

fun exe_ars_condsa (A1_, A2_, A3_, A4_, A5_) (B1_, B2_, B3_, B4_) (C1_, C2_)
  arss =
  distinct A3_ (map fst arss) andalso
    ball (ceq_list (ceq_prod B1_ (ceq_list C1_)),
           ccompare_list (ccompare_prod B2_ (ccompare_list C2_)))
      (image
        (ceq_prod A1_ (ceq_list (ceq_prod B1_ (ceq_list C1_))),
          ccompare_prod A2_
            (ccompare_list (ccompare_prod B2_ (ccompare_list C2_))))
        (ceq_list (ceq_prod B1_ (ceq_list C1_)),
          ccompare_list (ccompare_prod B2_ (ccompare_list C2_)), set_impl_list)
        snd (set (ceq_prod A1_ (ceq_list (ceq_prod B1_ (ceq_list C1_))),
                   ccompare_prod A2_
                     (ccompare_list (ccompare_prod B2_ (ccompare_list C2_))),
                   set_impl_prod A5_ set_impl_list)
              arss))
      (fn ars => distinct B3_ (map fst ars));

fun exe_ars_conds arss =
  exe_ars_condsa
    (ceq_literal, ccompare_literal, equal_literal, linorder_literal,
      set_impl_literal)
    (ceq_literal, ccompare_literal, equal_literal, linorder_literal)
    (ceq_set
       (cenum_literal, ceq_literal,
         ccompare_cproper_interval cproper_interval_literal),
      ccompare_set
        (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
          set_impl_literal))
    arss;

fun exe_osig_conds a = exe_class_conds (fst a) andalso exe_ars_conds (snd a);

fun wf_sort_set r f s =
  set_eq (cenum_literal, ceq_literal, ccompare_literal)
    (filter (ceq_literal, ccompare_literal)
      (fn c =>
        not (bex (ceq_literal, ccompare_literal) s
              (fn d =>
                member
                  (ceq_prod ceq_literal ceq_literal,
                    ccompare_prod ccompare_literal ccompare_literal)
                  (d, c) r andalso
                  not (member
                        (ceq_prod ceq_literal ceq_literal,
                          ccompare_prod ccompare_literal ccompare_literal)
                        (c, d) r))))
      s)
    s andalso
    less_eq_set (cenum_literal, ceq_literal, ccompare_literal) s f;

fun all_sorts_sets (A1_, A2_, A3_) (B1_, B2_, B3_) r f arss =
  ball (ceq_list
          (ceq_prod B1_
            (ceq_list
              (ceq_set
                (cenum_literal, ceq_literal,
                  ccompare_cproper_interval cproper_interval_literal)))),
         ccompare_list
           (ccompare_prod B2_
             (ccompare_list
               (ccompare_set
                 (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                   set_impl_literal)))))
    (image
      (ceq_prod A1_
         (ceq_list
           (ceq_prod B1_
             (ceq_list
               (ceq_set
                 (cenum_literal, ceq_literal,
                   ccompare_cproper_interval cproper_interval_literal))))),
        ccompare_prod A2_
          (ccompare_list
            (ccompare_prod B2_
              (ccompare_list
                (ccompare_set
                  (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                    set_impl_literal))))))
      (ceq_list
         (ceq_prod B1_
           (ceq_list
             (ceq_set
               (cenum_literal, ceq_literal,
                 ccompare_cproper_interval cproper_interval_literal)))),
        ccompare_list
          (ccompare_prod B2_
            (ccompare_list
              (ccompare_set
                (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                  set_impl_literal)))),
        set_impl_list)
      snd (set (ceq_prod A1_
                  (ceq_list
                    (ceq_prod B1_
                      (ceq_list
                        (ceq_set
                          (cenum_literal, ceq_literal,
                            ccompare_cproper_interval
                              cproper_interval_literal))))),
                 ccompare_prod A2_
                   (ccompare_list
                     (ccompare_prod B2_
                       (ccompare_list
                         (ccompare_set
                           (finite_UNIV_literal, ceq_literal,
                             cproper_interval_literal, set_impl_literal))))),
                 set_impl_prod A3_ set_impl_list)
            arss))
    (fn ars =>
      ball (ceq_list
              (ceq_set
                (cenum_literal, ceq_literal,
                  ccompare_cproper_interval cproper_interval_literal)),
             ccompare_list
               (ccompare_set
                 (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                   set_impl_literal)))
        (image
          (ceq_prod B1_
             (ceq_list
               (ceq_set
                 (cenum_literal, ceq_literal,
                   ccompare_cproper_interval cproper_interval_literal))),
            ccompare_prod B2_
              (ccompare_list
                (ccompare_set
                  (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                    set_impl_literal))))
          (ceq_list
             (ceq_set
               (cenum_literal, ceq_literal,
                 ccompare_cproper_interval cproper_interval_literal)),
            ccompare_list
              (ccompare_set
                (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                  set_impl_literal)),
            set_impl_list)
          snd (set (ceq_prod B1_
                      (ceq_list
                        (ceq_set
                          (cenum_literal, ceq_literal,
                            ccompare_cproper_interval
                              cproper_interval_literal))),
                     ccompare_prod B2_
                       (ccompare_list
                         (ccompare_set
                           (finite_UNIV_literal, ceq_literal,
                             cproper_interval_literal, set_impl_literal))),
                     set_impl_prod B3_ set_impl_list)
                ars))
        (list_all (wf_sort_set r f)));

fun all_sorts_relation (A1_, A2_, A3_) (B1_, B2_, B3_) r arss =
  all_sorts_sets (A1_, A2_, A3_) (B1_, B2_, B3_) r
    (field (ceq_literal, ccompare_literal, set_impl_literal) r) arss;

fun exe_all_normalized_and_ex_tcsigs (A1_, A2_, A3_) (B1_, B2_, B3_) cs arss =
  all_sorts_relation (A1_, A2_, A3_) (B1_, B2_, B3_)
    (set (ceq_prod ceq_literal ceq_literal,
           ccompare_prod ccompare_literal ccompare_literal,
           set_impl_prod set_impl_literal set_impl_literal)
      cs)
    arss;

fun exe_consistent_length_tcsigs (A1_, A2_, A3_) (B1_, B2_, B3_) (C1_, C2_) arss
  = ball (ceq_list (ceq_prod B1_ (ceq_list C1_)),
           ccompare_list (ccompare_prod B2_ (ccompare_list C2_)))
      (image
        (ceq_prod A1_ (ceq_list (ceq_prod B1_ (ceq_list C1_))),
          ccompare_prod A2_
            (ccompare_list (ccompare_prod B2_ (ccompare_list C2_))))
        (ceq_list (ceq_prod B1_ (ceq_list C1_)),
          ccompare_list (ccompare_prod B2_ (ccompare_list C2_)), set_impl_list)
        snd (set (ceq_prod A1_ (ceq_list (ceq_prod B1_ (ceq_list C1_))),
                   ccompare_prod A2_
                     (ccompare_list (ccompare_prod B2_ (ccompare_list C2_))),
                   set_impl_prod A3_ set_impl_list)
              arss))
      (fn ars =>
        ball (ceq_list C1_, ccompare_list C2_)
          (image
            (ceq_prod B1_ (ceq_list C1_), ccompare_prod B2_ (ccompare_list C2_))
            (ceq_list C1_, ccompare_list C2_, set_impl_list) snd
            (set (ceq_prod B1_ (ceq_list C1_),
                   ccompare_prod B2_ (ccompare_list C2_),
                   set_impl_prod B3_ set_impl_list)
              ars))
          (fn ss_1 =>
            ball (ceq_list C1_, ccompare_list C2_)
              (image
                (ceq_prod B1_ (ceq_list C1_),
                  ccompare_prod B2_ (ccompare_list C2_))
                (ceq_list C1_, ccompare_list C2_, set_impl_list) snd
                (set (ceq_prod B1_ (ceq_list C1_),
                       ccompare_prod B2_ (ccompare_list C2_),
                       set_impl_prod B3_ set_impl_list)
                  ars))
              (fn ss_2 => equal_nata (size_list ss_1) (size_list ss_2))));

fun coregular_rows r ars ks =
  ball (ceq_literal, ccompare_literal) ks
    (fn c1 =>
      ball (ceq_literal, ccompare_literal) ks
        (fn c2 =>
          (if class_leq (ceq_literal, ccompare_literal)
                (ceq_literal, ccompare_literal) r c1 c2
            then list_all2
                   (sort_leq (ceq_literal, ccompare_literal)
                     (ceq_literal, ccompare_literal) r)
                   (the (lookupa (fn x => ((x : string) = c1)) ars))
                   (the (lookupa (fn x => ((x : string) = c2)) ars))
            else true)));

fun coregular_arity r ars =
  coregular_rows r ars
    (image
      (ceq_prod ceq_literal
         (ceq_list
           (ceq_set
             (cenum_literal, ceq_literal,
               ccompare_cproper_interval cproper_interval_literal))),
        ccompare_prod ccompare_literal
          (ccompare_list
            (ccompare_set
              (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                set_impl_literal))))
      (ceq_literal, ccompare_literal, set_impl_literal) fst
      (set (ceq_prod ceq_literal
              (ceq_list
                (ceq_set
                  (cenum_literal, ceq_literal,
                    ccompare_cproper_interval cproper_interval_literal))),
             ccompare_prod ccompare_literal
               (ccompare_list
                 (ccompare_set
                   (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                     set_impl_literal))),
             set_impl_prod set_impl_literal set_impl_list)
        ars));

fun coregular_set (A1_, A2_, A3_) r arss =
  ball (ceq_list
          (ceq_prod ceq_literal
            (ceq_list
              (ceq_set
                (cenum_literal, ceq_literal,
                  ccompare_cproper_interval cproper_interval_literal)))),
         ccompare_list
           (ccompare_prod ccompare_literal
             (ccompare_list
               (ccompare_set
                 (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                   set_impl_literal)))))
    (image
      (ceq_prod A1_
         (ceq_list
           (ceq_prod ceq_literal
             (ceq_list
               (ceq_set
                 (cenum_literal, ceq_literal,
                   ccompare_cproper_interval cproper_interval_literal))))),
        ccompare_prod A2_
          (ccompare_list
            (ccompare_prod ccompare_literal
              (ccompare_list
                (ccompare_set
                  (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                    set_impl_literal))))))
      (ceq_list
         (ceq_prod ceq_literal
           (ceq_list
             (ceq_set
               (cenum_literal, ceq_literal,
                 ccompare_cproper_interval cproper_interval_literal)))),
        ccompare_list
          (ccompare_prod ccompare_literal
            (ccompare_list
              (ccompare_set
                (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                  set_impl_literal)))),
        set_impl_list)
      snd (set (ceq_prod A1_
                  (ceq_list
                    (ceq_prod ceq_literal
                      (ceq_list
                        (ceq_set
                          (cenum_literal, ceq_literal,
                            ccompare_cproper_interval
                              cproper_interval_literal))))),
                 ccompare_prod A2_
                   (ccompare_list
                     (ccompare_prod ccompare_literal
                       (ccompare_list
                         (ccompare_set
                           (finite_UNIV_literal, ceq_literal,
                             cproper_interval_literal, set_impl_literal))))),
                 set_impl_prod A3_ set_impl_list)
            arss))
    (coregular_arity r);

fun exe_coregular_tcsigs (A1_, A2_, A3_) cs arss =
  coregular_set (A1_, A2_, A3_)
    (set (ceq_prod ceq_literal ceq_literal,
           ccompare_prod ccompare_literal ccompare_literal,
           set_impl_prod set_impl_literal set_impl_literal)
      cs)
    arss;

fun complete_keys (A1_, A2_) cs ks =
  list_all
    (fn (c1, c2) =>
      (if member (A1_, A2_) c1 ks then member (A1_, A2_) c2 ks else true))
    cs;

fun complete_arity (A1_, A2_, A3_) (B1_, B2_, B3_) cs ars =
  complete_keys (A1_, A2_) cs
    (image (ceq_prod A1_ B1_, ccompare_prod A2_ B2_) (A1_, A2_, A3_) fst
      (set (ceq_prod A1_ B1_, ccompare_prod A2_ B2_, set_impl_prod A3_ B3_)
        ars));

fun complete_set (A1_, A2_, A3_) (B1_, B2_, B3_) (C1_, C2_, C3_) cs arss =
  ball (ceq_list (ceq_prod A1_ C1_), ccompare_list (ccompare_prod A2_ C2_))
    (image
      (ceq_prod B1_ (ceq_list (ceq_prod A1_ C1_)),
        ccompare_prod B2_ (ccompare_list (ccompare_prod A2_ C2_)))
      (ceq_list (ceq_prod A1_ C1_), ccompare_list (ccompare_prod A2_ C2_),
        set_impl_list)
      snd (set (ceq_prod B1_ (ceq_list (ceq_prod A1_ C1_)),
                 ccompare_prod B2_ (ccompare_list (ccompare_prod A2_ C2_)),
                 set_impl_prod B3_ set_impl_list)
            arss))
    (complete_arity (A1_, A2_, A3_) (C1_, C2_, C3_) cs);

fun exe_complete_tcsigs (A1_, A2_, A3_) (B1_, B2_, B3_) (C1_, C2_, C3_) cs arss
  = complete_set (A1_, A2_, A3_) (B1_, B2_, B3_) (C1_, C2_, C3_) cs arss;

fun exe_wf_tcsigs (A1_, A2_, A3_) cs arss =
  exe_coregular_tcsigs (A1_, A2_, A3_) cs arss andalso
    (exe_complete_tcsigs (ceq_literal, ccompare_literal, set_impl_literal)
       (A1_, A2_, A3_)
       (ceq_list
          (ceq_set
            (cenum_literal, ceq_literal,
              ccompare_cproper_interval cproper_interval_literal)),
         ccompare_list
           (ccompare_set
             (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
               set_impl_literal)),
         set_impl_list)
       cs arss andalso
      (exe_consistent_length_tcsigs (A1_, A2_, A3_)
         (ceq_literal, ccompare_literal, set_impl_literal)
         (ceq_set
            (cenum_literal, ceq_literal,
              ccompare_cproper_interval cproper_interval_literal),
           ccompare_set
             (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
               set_impl_literal))
         arss andalso
        exe_all_normalized_and_ex_tcsigs (A1_, A2_, A3_)
          (ceq_literal, ccompare_literal, set_impl_literal) cs arss));

fun exe_wf_osig oss =
  exe_wf_subclass
    (cenum_literal, ceq_literal, ccompare_literal, equal_literal,
      set_impl_literal)
    (fst oss) andalso
    (exe_wf_tcsigs (ceq_literal, ccompare_literal, set_impl_literal) (fst oss)
       (snd oss) andalso
      exe_osig_conds oss);

fun exe_wf_siga (ExeSignature (cto, tao, sa)) =
  exe_wf_osig sa andalso
    (set_eq (cenum_literal, ceq_literal, ccompare_literal)
       (image
         (ceq_prod ceq_literal
            (ceq_list
              (ceq_prod ceq_literal
                (ceq_list
                  (ceq_set
                    (cenum_literal, ceq_literal,
                      ccompare_cproper_interval cproper_interval_literal))))),
           ccompare_prod ccompare_literal
             (ccompare_list
               (ccompare_prod ccompare_literal
                 (ccompare_list
                   (ccompare_set
                     (finite_UNIV_literal, ceq_literal,
                       cproper_interval_literal, set_impl_literal))))))
         (ceq_literal, ccompare_literal, set_impl_literal) fst
         (set (ceq_prod ceq_literal
                 (ceq_list
                   (ceq_prod ceq_literal
                     (ceq_list
                       (ceq_set
                         (cenum_literal, ceq_literal,
                           ccompare_cproper_interval
                             cproper_interval_literal))))),
                ccompare_prod ccompare_literal
                  (ccompare_list
                    (ccompare_prod ccompare_literal
                      (ccompare_list
                        (ccompare_set
                          (finite_UNIV_literal, ceq_literal,
                            cproper_interval_literal, set_impl_literal))))),
                set_impl_prod set_impl_literal set_impl_list)
           (snd sa)))
       (image
         (ceq_prod ceq_literal ceq_nat,
           ccompare_prod ccompare_literal ccompare_nat)
         (ceq_literal, ccompare_literal, set_impl_literal) fst
         (set (ceq_prod ceq_literal ceq_nat,
                ccompare_prod ccompare_literal ccompare_nat,
                set_impl_prod set_impl_literal set_impl_nat)
           tao)) andalso
      (ball (ceq_literal, ccompare_literal)
         (image
           (ceq_prod ceq_literal
              (ceq_list
                (ceq_prod ceq_literal
                  (ceq_list
                    (ceq_set
                      (cenum_literal, ceq_literal,
                        ccompare_cproper_interval cproper_interval_literal))))),
             ccompare_prod ccompare_literal
               (ccompare_list
                 (ccompare_prod ccompare_literal
                   (ccompare_list
                     (ccompare_set
                       (finite_UNIV_literal, ceq_literal,
                         cproper_interval_literal, set_impl_literal))))))
           (ceq_literal, ccompare_literal, set_impl_literal) fst
           (set (ceq_prod ceq_literal
                   (ceq_list
                     (ceq_prod ceq_literal
                       (ceq_list
                         (ceq_set
                           (cenum_literal, ceq_literal,
                             ccompare_cproper_interval
                               cproper_interval_literal))))),
                  ccompare_prod ccompare_literal
                    (ccompare_list
                      (ccompare_prod ccompare_literal
                        (ccompare_list
                          (ccompare_set
                            (finite_UNIV_literal, ceq_literal,
                              cproper_interval_literal, set_impl_literal))))),
                  set_impl_prod set_impl_literal set_impl_list)
             (snd sa)))
         (fn typea =>
           ball (ceq_list
                   (ceq_set
                     (cenum_literal, ceq_literal,
                       ccompare_cproper_interval cproper_interval_literal)),
                  ccompare_list
                    (ccompare_set
                      (finite_UNIV_literal, ceq_literal,
                        cproper_interval_literal, set_impl_literal)))
             (image
               (ceq_prod ceq_literal
                  (ceq_list
                    (ceq_set
                      (cenum_literal, ceq_literal,
                        ccompare_cproper_interval cproper_interval_literal))),
                 ccompare_prod ccompare_literal
                   (ccompare_list
                     (ccompare_set
                       (finite_UNIV_literal, ceq_literal,
                         cproper_interval_literal, set_impl_literal))))
               (ceq_list
                  (ceq_set
                    (cenum_literal, ceq_literal,
                      ccompare_cproper_interval cproper_interval_literal)),
                 ccompare_list
                   (ccompare_set
                     (finite_UNIV_literal, ceq_literal,
                       cproper_interval_literal, set_impl_literal)),
                 set_impl_list)
               snd (set (ceq_prod ceq_literal
                           (ceq_list
                             (ceq_set
                               (cenum_literal, ceq_literal,
                                 ccompare_cproper_interval
                                   cproper_interval_literal))),
                          ccompare_prod ccompare_literal
                            (ccompare_list
                              (ccompare_set
                                (finite_UNIV_literal, ceq_literal,
                                  cproper_interval_literal, set_impl_literal))),
                          set_impl_prod set_impl_literal set_impl_list)
                     (the (lookupa (fn k => ((k : string) = typea)) (snd sa)))))
             (fn ars =>
               equal_nata (the (lookupa (fn k => ((k : string) = typea)) tao))
                 (size_list ars))) andalso
        ball (ceq_typ, ccompare_typ)
          (image
            (ceq_prod ceq_literal ceq_typ,
              ccompare_prod ccompare_literal ccompare_typ)
            (ceq_typ, ccompare_typ, set_impl_typ) snd
            (set (ceq_prod ceq_literal ceq_typ,
                   ccompare_prod ccompare_literal ccompare_typ,
                   set_impl_prod set_impl_literal set_impl_typ)
              cto))
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
(Fv (Var ("x", zero_int),
      Tv (Var ("'a", zero_int),
           set_empty (ceq_literal, ccompare_literal)
             (of_phantom set_impl_literala))))),
                                   Ty ("fun",
[the (typ_of
       (Fv (Var ("y", zero_int),
             Tv (Var ("'a", zero_int),
                  set_empty (ceq_literal, ccompare_literal)
                    (of_phantom set_impl_literala))))),
  Ty ("prop", [])])])),
                        Fv (Var ("x", zero_int),
                             Tv (Var ("'a", zero_int),
                                  set_empty (ceq_literal, ccompare_literal)
                                    (of_phantom set_impl_literala)))),
                   Fv (Var ("y", zero_int),
                        Tv (Var ("'a", zero_int),
                             set_empty (ceq_literal, ccompare_literal)
                               (of_phantom set_impl_literala))))),
        App (App (Ct ("Pure.imp",
                       Ty ("fun",
                            [Ty ("prop", []),
                              Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
                   App (App (Ct ("Pure.eq",
                                  Ty ("fun",
                                       [the
  (typ_of
    (Fv (Var ("y", zero_int),
          Tv (Var ("'a", zero_int),
               set_empty (ceq_literal, ccompare_literal)
                 (of_phantom set_impl_literala))))),
 Ty ("fun",
      [the (typ_of
             (Fv (Var ("z", zero_int),
                   Tv (Var ("'a", zero_int),
                        set_empty (ceq_literal, ccompare_literal)
                          (of_phantom set_impl_literala))))),
        Ty ("prop", [])])])),
                              Fv (Var ("y", zero_int),
                                   Tv (Var ("'a", zero_int),
set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala)))),
                         Fv (Var ("z", zero_int),
                              Tv (Var ("'a", zero_int),
                                   set_empty (ceq_literal, ccompare_literal)
                                     (of_phantom set_impl_literala))))),
              App (App (Ct ("Pure.eq",
                             Ty ("fun",
                                  [the (typ_of
 (Fv (Var ("x", zero_int),
       Tv (Var ("'a", zero_int),
            set_empty (ceq_literal, ccompare_literal)
              (of_phantom set_impl_literala))))),
                                    Ty ("fun",
 [the (typ_of
        (Fv (Var ("z", zero_int),
              Tv (Var ("'a", zero_int),
                   set_empty (ceq_literal, ccompare_literal)
                     (of_phantom set_impl_literala))))),
   Ty ("prop", [])])])),
                         Fv (Var ("x", zero_int),
                              Tv (Var ("'a", zero_int),
                                   set_empty (ceq_literal, ccompare_literal)
                                     (of_phantom set_impl_literala)))),
                    Fv (Var ("z", zero_int),
                         Tv (Var ("'a", zero_int),
                              set_empty (ceq_literal, ccompare_literal)
                                (of_phantom set_impl_literala))))));

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
           [Tv (Var ("'a", zero_int),
                 set_empty (ceq_literal, ccompare_literal)
                   (of_phantom set_impl_literala)),
             Tv (Var ("'b", zero_int),
                  set_empty (ceq_literal, ccompare_literal)
                    (of_phantom set_impl_literala))])))),
                                   Ty ("fun",
[the (typ_of
       (Fv (Var ("g", zero_int),
             Ty ("fun",
                  [Tv (Var ("'a", zero_int),
                        set_empty (ceq_literal, ccompare_literal)
                          (of_phantom set_impl_literala)),
                    Tv (Var ("'b", zero_int),
                         set_empty (ceq_literal, ccompare_literal)
                           (of_phantom set_impl_literala))])))),
  Ty ("prop", [])])])),
                        Fv (Var ("f", zero_int),
                             Ty ("fun",
                                  [Tv (Var ("'a", zero_int),
set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala)),
                                    Tv (Var ("'b", zero_int),
 set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala))]))),
                   Fv (Var ("g", zero_int),
                        Ty ("fun",
                             [Tv (Var ("'a", zero_int),
                                   set_empty (ceq_literal, ccompare_literal)
                                     (of_phantom set_impl_literala)),
                               Tv (Var ("'b", zero_int),
                                    set_empty (ceq_literal, ccompare_literal)
                                      (of_phantom set_impl_literala))])))),
        App (App (Ct ("Pure.imp",
                       Ty ("fun",
                            [Ty ("prop", []),
                              Ty ("fun", [Ty ("prop", []), Ty ("prop", [])])])),
                   App (App (Ct ("Pure.eq",
                                  Ty ("fun",
                                       [the
  (typ_of
    (Fv (Var ("x", zero_int),
          Tv (Var ("'a", zero_int),
               set_empty (ceq_literal, ccompare_literal)
                 (of_phantom set_impl_literala))))),
 Ty ("fun",
      [the (typ_of
             (Fv (Var ("y", zero_int),
                   Tv (Var ("'a", zero_int),
                        set_empty (ceq_literal, ccompare_literal)
                          (of_phantom set_impl_literala))))),
        Ty ("prop", [])])])),
                              Fv (Var ("x", zero_int),
                                   Tv (Var ("'a", zero_int),
set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala)))),
                         Fv (Var ("y", zero_int),
                              Tv (Var ("'a", zero_int),
                                   set_empty (ceq_literal, ccompare_literal)
                                     (of_phantom set_impl_literala))))),
              App (App (Ct ("Pure.eq",
                             Ty ("fun",
                                  [the (typ_of
 (App (Fv (Var ("f", zero_int),
            Ty ("fun",
                 [Tv (Var ("'a", zero_int),
                       set_empty (ceq_literal, ccompare_literal)
                         (of_phantom set_impl_literala)),
                   Tv (Var ("'b", zero_int),
                        set_empty (ceq_literal, ccompare_literal)
                          (of_phantom set_impl_literala))])),
        Fv (Var ("x", zero_int),
             Tv (Var ("'a", zero_int),
                  set_empty (ceq_literal, ccompare_literal)
                    (of_phantom set_impl_literala)))))),
                                    Ty ("fun",
 [the (typ_of
        (App (Fv (Var ("g", zero_int),
                   Ty ("fun",
                        [Tv (Var ("'a", zero_int),
                              set_empty (ceq_literal, ccompare_literal)
                                (of_phantom set_impl_literala)),
                          Tv (Var ("'b", zero_int),
                               set_empty (ceq_literal, ccompare_literal)
                                 (of_phantom set_impl_literala))])),
               Fv (Var ("y", zero_int),
                    Tv (Var ("'a", zero_int),
                         set_empty (ceq_literal, ccompare_literal)
                           (of_phantom set_impl_literala)))))),
   Ty ("prop", [])])])),
                         App (Fv (Var ("f", zero_int),
                                   Ty ("fun",
[Tv (Var ("'a", zero_int),
      set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala)),
  Tv (Var ("'b", zero_int),
       set_empty (ceq_literal, ccompare_literal)
         (of_phantom set_impl_literala))])),
                               Fv (Var ("x", zero_int),
                                    Tv (Var ("'a", zero_int),
 set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala))))),
                    App (Fv (Var ("g", zero_int),
                              Ty ("fun",
                                   [Tv (Var ("'a", zero_int),
 set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala)),
                                     Tv (Var ("'b", zero_int),
  set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala))])),
                          Fv (Var ("y", zero_int),
                               Tv (Var ("'a", zero_int),
                                    set_empty (ceq_literal, ccompare_literal)
                                      (of_phantom set_impl_literala)))))));

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
                                  [Tv (Var ("'a", zero_int),
set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala)),
                                    Ty ("prop", [])]),
                              Ty ("prop", [])])),
                   Abs (Tv (Var ("'a", zero_int),
                             set_empty (ceq_literal, ccompare_literal)
                               (of_phantom set_impl_literala)),
                         App (App (Ct ("Pure.eq",
Ty ("fun",
     [Tv (Var ("'b", zero_int),
           set_empty (ceq_literal, ccompare_literal)
             (of_phantom set_impl_literala)),
       Ty ("fun",
            [Tv (Var ("'b", zero_int),
                  set_empty (ceq_literal, ccompare_literal)
                    (of_phantom set_impl_literala)),
              Ty ("prop", [])])])),
                                    App (Fv
   (Var ("f", zero_int),
     Ty ("fun",
          [Tv (Var ("'a", zero_int),
                set_empty (ceq_literal, ccompare_literal)
                  (of_phantom set_impl_literala)),
            Tv (Var ("'b", zero_int),
                 set_empty (ceq_literal, ccompare_literal)
                   (of_phantom set_impl_literala))])),
  Bv zero_nat)),
                               App (Fv (Var ("g", zero_int),
 Ty ("fun",
      [Tv (Var ("'a", zero_int),
            set_empty (ceq_literal, ccompare_literal)
              (of_phantom set_impl_literala)),
        Tv (Var ("'b", zero_int),
             set_empty (ceq_literal, ccompare_literal)
               (of_phantom set_impl_literala))])),
                                     Bv zero_nat))))),
        App (App (Ct ("Pure.eq",
                       Ty ("fun",
                            [the (typ_of
                                   (Abs (Tv
   (Var ("'a", zero_int),
     set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala)),
  App (Fv (Var ("f", zero_int),
            Ty ("fun",
                 [Tv (Var ("'a", zero_int),
                       set_empty (ceq_literal, ccompare_literal)
                         (of_phantom set_impl_literala)),
                   Tv (Var ("'b", zero_int),
                        set_empty (ceq_literal, ccompare_literal)
                          (of_phantom set_impl_literala))])),
        Bv zero_nat)))),
                              Ty ("fun",
                                   [the (typ_of
  (Abs (Tv (Var ("'a", zero_int),
             set_empty (ceq_literal, ccompare_literal)
               (of_phantom set_impl_literala)),
         App (Fv (Var ("g", zero_int),
                   Ty ("fun",
                        [Tv (Var ("'a", zero_int),
                              set_empty (ceq_literal, ccompare_literal)
                                (of_phantom set_impl_literala)),
                          Tv (Var ("'b", zero_int),
                               set_empty (ceq_literal, ccompare_literal)
                                 (of_phantom set_impl_literala))])),
               Bv zero_nat)))),
                                     Ty ("prop", [])])])),
                   Abs (Tv (Var ("'a", zero_int),
                             set_empty (ceq_literal, ccompare_literal)
                               (of_phantom set_impl_literala)),
                         App (Fv (Var ("f", zero_int),
                                   Ty ("fun",
[Tv (Var ("'a", zero_int),
      set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala)),
  Tv (Var ("'b", zero_int),
       set_empty (ceq_literal, ccompare_literal)
         (of_phantom set_impl_literala))])),
                               Bv zero_nat))),
              Abs (Tv (Var ("'a", zero_int),
                        set_empty (ceq_literal, ccompare_literal)
                          (of_phantom set_impl_literala)),
                    App (Fv (Var ("g", zero_int),
                              Ty ("fun",
                                   [Tv (Var ("'a", zero_int),
 set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala)),
                                     Tv (Var ("'b", zero_int),
  set_empty (ceq_literal, ccompare_literal) (of_phantom set_impl_literala))])),
                          Bv zero_nat))));

fun exeis_std_sig (ExeSignature (cto, tao, sorts)) =
  equal_option equal_nat (lookupa (fn k => ((k : string) = "fun")) tao)
    (SOME (nat_of_integer (2 : IntInf.int))) andalso
    (equal_option equal_nat (lookupa (fn k => ((k : string) = "prop")) tao)
       (SOME zero_nat) andalso
      (equal_option equal_nat (lookupa (fn k => ((k : string) = "itself")) tao)
         (SOME one_nat) andalso
        (equal_option equal_typ
           (lookupa (fn k => ((k : string) = "Pure.eq")) cto)
           (SOME (Ty ("fun",
                       [Tv (Var ("'a", zero_int),
                             set_empty (ceq_literal, ccompare_literal)
                               (of_phantom set_impl_literala)),
                         Ty ("fun",
                              [Tv (Var ("'a", zero_int),
                                    set_empty (ceq_literal, ccompare_literal)
                                      (of_phantom set_impl_literala)),
                                Ty ("prop", [])])]))) andalso
          (equal_option equal_typ
             (lookupa (fn k => ((k : string) = "Pure.all")) cto)
             (SOME (Ty ("fun",
                         [Ty ("fun",
                               [Tv (Var ("'a", zero_int),
                                     set_empty (ceq_literal, ccompare_literal)
                                       (of_phantom set_impl_literala)),
                                 Ty ("prop", [])]),
                           Ty ("prop", [])]))) andalso
            (equal_option equal_typ
               (lookupa (fn k => ((k : string) = "Pure.imp")) cto)
               (SOME (Ty ("fun",
                           [Ty ("prop", []),
                             Ty ("fun",
                                  [Ty ("prop", []),
                                    Ty ("prop", [])])]))) andalso
              equal_option equal_typ
                (lookupa (fn k => ((k : string) = "Pure.type")) cto)
                (SOME (Ty ("itself",
                            [Tv (Var ("'a", zero_int),
                                  set_empty (ceq_literal, ccompare_literal)
                                    (of_phantom set_impl_literala))]))))))));

fun exe_wf_theorya (ExeTheory (ExeSignature (cto, tao, sa), ax)) =
  exe_sig_conds (ExeSignature (cto, tao, sa)) andalso
    (list_all
       (fn p =>
         exeterm_oka (ExeSignature (cto, tao, sa)) p andalso
           equal_option equal_typ (typ_of p) (SOME (Ty ("prop", []))))
       ax andalso
      (exeis_std_sig (ExeSignature (cto, tao, sa)) andalso
        (exe_wf_sig (ExeSignature (cto, tao, sa)) andalso
          less_eq_set (cenum_term, ceq_term, ccompare_term)
            (insert (ceq_term, ccompare_term) eq_reflexive_ax
              (insert (ceq_term, ccompare_term) eq_symmetric_ax
                (insert (ceq_term, ccompare_term) eq_transitive_ax
                  (insert (ceq_term, ccompare_term) eq_intr_ax
                    (insert (ceq_term, ccompare_term) eq_elim_ax
                      (insert (ceq_term, ccompare_term) eq_combination_ax
                        (insert (ceq_term, ccompare_term) eq_abstract_rule_ax
                          (set_empty (ceq_term, ccompare_term)
                            (of_phantom set_impl_terma)))))))))
            (set (ceq_term, ccompare_term, set_impl_term) ax))));

fun exe_wf_theory theta = exe_wf_theorya theta;

fun exe_check_proof e p res =
  exe_wf_theorya e andalso equal_option equal_term (exereplay e p) (SOME res);

fun int n = Int_of_integer n;

fun nat n = nat_of_integer n;

fun sort xs = set (ceq_literal, ccompare_literal, set_impl_literal) xs;

end; (*struct ExportCheck*)

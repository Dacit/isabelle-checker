theory Checker_Export
  imports
    Metalogic_ProofChecker.CodeGen
    Containers.Containers
begin

section \<open>Constants for better Interface\<close>

definition int :: "integer \<Rightarrow> int" where
  "int n = int_of_integer n"

definition nat :: "integer \<Rightarrow> nat" where
  "nat n = nat_of_integer n"

definition sort :: "String.literal list \<Rightarrow> sort" where
  "sort xs = set xs"

definition eq_term :: "term \<Rightarrow> term \<Rightarrow> bool" where
  "eq_term t1 t2 \<equiv> t1 = t2"


section \<open>Containers Setup\<close>

subsection \<open>Derive containers instances for \<^typ>\<open>variable\<close>, \<^typ>\<open>typ\<close>, and \<^typ>\<open>term\<close>\<close>

derive (eq) ceq "variable" "typ" "term"
derive ccompare "variable"
derive (no) ccompare "typ" "term"
derive (rbt) set_impl "variable"
derive (choose) set_impl "typ" "term"
derive (no) cenum "variable" "typ" "term"


subsection \<open>infinitudes\<close>

lemma infinite_from_literal:
  fixes f :: "String.literal \<Rightarrow> 'a"
  assumes "inj f"
  shows "infinite (UNIV :: 'a set)"
proof -
  have "infinite (f ` UNIV)"
    using assms infinite_literal by (simp add: finite_image_iff)
  then show ?thesis by (meson finite_subset subset_UNIV)
qed

lemma infinite_variable: "infinite (UNIV :: variable set)"
  by (rule infinite_from_literal[where f = Free]) (simp add: inj_def)

lemma infinite_typ: "infinite (UNIV :: typ set)"
  by (rule infinite_from_literal[where f = "\<lambda>n. Ty n []"]) (simp add: inj_def)

lemma infinite_term: "infinite (UNIV :: term set)"
  by (rule infinite_from_literal[where f = "\<lambda>n. Ct n propT"]) (simp add: inj_def)


subsection \<open>Mark universes as non-finite\<close>

instantiation variable :: card_UNIV
begin
definition "finite_UNIV = Phantom(variable) False"
definition "card_UNIV = Phantom(variable) 0"
instance by intro_classes
  (simp_all add: finite_UNIV_variable_def card_UNIV_variable_def infinite_variable)
end

instantiation "typ" :: card_UNIV
begin
definition "finite_UNIV = Phantom(typ) False"
definition "card_UNIV = Phantom(typ) 0"
instance by intro_classes
  (simp_all add: finite_UNIV_typ_def card_UNIV_typ_def infinite_typ)
end

instantiation "term" :: card_UNIV
begin
definition "finite_UNIV = Phantom(term) False"
definition "card_UNIV = Phantom(term) 0"
instance by intro_classes
  (simp_all add: finite_UNIV_term_def card_UNIV_term_def infinite_term)
end


subsection \<open>Needed by set operations, emtpy here\<close>

instantiation variable :: cproper_interval
begin
definition cproper_interval_variable :: "variable proper_interval" where
  "cproper_interval_variable _ _ = False"
instance by intro_classes (simp add: infinite_variable)
end

instantiation "typ" :: cproper_interval
begin
definition cproper_interval_typ :: "typ proper_interval" where
  "cproper_interval_typ _ _ = False"
instance by intro_classes (simp add: infinite_typ)
end

instantiation "term" :: cproper_interval
begin
definition cproper_interval_term :: "term proper_interval" where
  "cproper_interval_term _ _ = False"
instance by intro_classes (simp add: infinite_term)
end


section \<open>Adapted code setup\<close>

text \<open>Avoid building set multiple times\<close>

definition coregular_rows ::
  "(class \<times> class) set \<Rightarrow> (class \<times> sort list) list \<Rightarrow> class set \<Rightarrow> bool" where
  "coregular_rows r ars ks \<longleftrightarrow>
    (\<forall>c1 \<in> ks. \<forall>c2 \<in> ks.
      class_leq r c1 c2 \<longrightarrow>
        list_all2 (sort_leq r)
          (the (lookup (\<lambda>x. x = c1) ars)) (the (lookup (\<lambda>x. x = c2) ars)))"

definition coregular_arity ::
  "(class \<times> class) set \<Rightarrow> (class \<times> sort list) list \<Rightarrow> bool" where
  "coregular_arity r ars = coregular_rows r ars (fst ` set ars)"

definition coregular_set ::
  "(class \<times> class) set \<Rightarrow> ('a \<times> (class \<times> sort list) list) list \<Rightarrow> bool" where
  "coregular_set r arss \<longleftrightarrow>
    (\<forall>ars \<in> snd ` set arss. coregular_arity r ars)"

declare [[code drop: exe_coregular_tcsigs]]
lemma coregular_code[code]:
  "exe_coregular_tcsigs cs arss = coregular_set (set cs) arss"
  by (simp add: exe_coregular_tcsigs_def coregular_set_def
    coregular_arity_def coregular_rows_def)


text \<open>Lift to sets\<close>

declare [[code drop: exesort_ex]]
lemma sort_exists_code[code]:
  "exesort_ex cs s = (s \<subseteq> Field (set cs))"
  by (auto simp add: Field_set_code subset_iff)

definition complete_keys :: "('a \<times> 'a) list \<Rightarrow> 'a set \<Rightarrow> bool" where
  "complete_keys cs ks \<longleftrightarrow>
    list_all (\<lambda>(c1,c2). c1 \<in> ks \<longrightarrow> c2 \<in> ks) cs"

definition complete_arity :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'c) list \<Rightarrow> bool" where
  "complete_arity cs ars = complete_keys cs (fst ` set ars)"

definition complete_set ::
  "('a \<times> 'a) list \<Rightarrow> ('b \<times> ('a \<times> 'c) list) list \<Rightarrow> bool" where
  "complete_set cs arss \<longleftrightarrow>
    (\<forall>ars \<in> snd ` set arss. complete_arity cs ars)"

declare [[code drop: exe_complete_tcsigs]]
lemma complete_code[code]:
  "exe_complete_tcsigs cs arss = complete_set cs arss"
  by (auto simp add: exe_complete_tcsigs_def complete_set_def
    complete_arity_def complete_keys_def list_all_iff)

definition wf_sort_set :: "(class \<times> class) set \<Rightarrow> class set \<Rightarrow> sort \<Rightarrow> bool" where
  "wf_sort_set r f s \<longleftrightarrow> ({c \<in> s. \<not> (\<exists>d \<in> s. (d,c) \<in> r \<and> (c,d) \<notin> r)} = s \<and> s \<subseteq> f)"

lemma wf_sort_correct:
  "exewf_sort cs s = wf_sort_set (set cs) (Field (set cs)) s"
  by (auto simp add: wf_sort_set_def Field_set_code subset_iff)

definition all_sorts_sets ::
  "(class \<times> class) set \<Rightarrow> class set \<Rightarrow>
    ('a \<times> ('b \<times> sort list) list) list \<Rightarrow> bool" where
  "all_sorts_sets r f arss \<longleftrightarrow>
    (\<forall>ars \<in> snd ` set arss. \<forall>ss \<in> snd ` set ars.
      \<forall>s \<in> set ss. wf_sort_set r f s)"

definition all_sorts_relation ::
  "(class \<times> class) set \<Rightarrow> ('a \<times> ('b \<times> sort list) list) list \<Rightarrow> bool" where
  "all_sorts_relation r arss = all_sorts_sets r (Field r) arss"

declare [[code drop: exe_all_normalized_and_ex_tcsigs]]
lemma all_sorts_code[code]:
  "exe_all_normalized_and_ex_tcsigs cs arss = all_sorts_relation (set cs) arss"
  by (simp only: exe_all_normalized_and_ex_tcsigs_def all_sorts_relation_def
    all_sorts_sets_def wf_sort_correct)


text \<open>Share the subclass relation and its field when checking constant types.\<close>

fun typ_ok_prepared ::
  "(name \<times> nat) list \<Rightarrow> (class \<times> class) set \<Rightarrow> class set \<Rightarrow> typ \<Rightarrow> bool" where
  "typ_ok_prepared arities r f (Ty c Ts) =
    (case lookup (\<lambda>k. k = c) arities of
       None \<Rightarrow> False
     | Some ar \<Rightarrow> length Ts = ar \<and> list_all (typ_ok_prepared arities r f) Ts)"
| "typ_ok_prepared arities r f (Tv v S) = wf_sort_set r f S"

lemma typ_ok_prepared_correct:
  "typ_ok_prepared (exetyp_arity_of \<Sigma>)
      (set (execlasses (exesorts \<Sigma>)))
      (Field (set (execlasses (exesorts \<Sigma>)))) T = exetyp_ok_sig \<Sigma> T"
  by (induction T)
    (auto simp only: typ_ok_prepared.simps exetyp_ok_sig.simps
      wf_sort_correct list_all_iff split: option.splits)

definition const_types_ok ::
  "(name \<times> nat) list \<Rightarrow> (class \<times> class) set \<Rightarrow> class set \<Rightarrow>
    (name \<times> typ) list \<Rightarrow> bool" where
  "const_types_ok arities r f cto =
    list_all (\<lambda>(_, T). typ_ok_prepared arities r f T) cto"

definition const_types_relation ::
  "(name \<times> nat) list \<Rightarrow> (class \<times> class) set \<Rightarrow>
    (name \<times> typ) list \<Rightarrow> bool" where
  "const_types_relation arities r cto = const_types_ok arities r (Field r) cto"

lemma const_types_relation_correct:
  "const_types_relation tao (set (execlasses sa)) cto =
    (\<forall>T \<in> snd ` set cto. exetyp_ok_sig (ExeSignature cto tao sa) T)"
  unfolding const_types_relation_def const_types_ok_def
  by (simp add: typ_ok_prepared_correct[symmetric] list_all_iff split_def)

declare [[code drop: exe_wf_sig]]
lemma wf_sig_shared_code[code]:
  "exe_wf_sig (ExeSignature cto tao sa) =
    (exe_wf_osig sa \<and>
     fst ` set (exetcsigs sa) = fst ` set tao \<and>
     (\<forall>type \<in> fst ` set (exetcsigs sa).
       \<forall>ars \<in> snd ` set (the (lookup (\<lambda>k. k = type) (exetcsigs sa))).
         the (lookup (\<lambda>k. k = type) tao) = length ars) \<and>
     const_types_relation tao (set (execlasses sa)) cto)"
  by (simp only: exe_wf_sig_code exe_wf_sig'.simps const_types_relation_correct)


text \<open>Index constant and type constructor lookups once per validation.\<close>

fun typ_ok_mapped ::
  "(name, nat) mapping \<Rightarrow> (class \<times> class) set \<Rightarrow> class set \<Rightarrow> typ \<Rightarrow> bool" where
  "typ_ok_mapped arities r f (Ty c Ts) =
    (case Mapping.lookup arities c of None \<Rightarrow> False
     | Some ar \<Rightarrow> length Ts = ar \<and> list_all (typ_ok_mapped arities r f) Ts)"
| "typ_ok_mapped arities r f (Tv v S) = wf_sort_set r f S"

lemma typ_ok_mapped_correct:
  "typ_ok_mapped (Mapping.of_alist arities) r f T = typ_ok_prepared arities r f T"
  by (induction T)
    (auto simp only: typ_ok_mapped.simps typ_ok_prepared.simps
      Mapping.lookup_of_alist lookup_eq_map_of_ap list_all_iff split: option.splits)

declare [[code drop: const_types_ok]]
lemma const_types_mapped_code[code]:
  "const_types_ok arities r f cto =
    list_all (typ_ok_mapped (Mapping.of_alist arities) r f) (map snd cto)"
  by (auto simp add: const_types_ok_def typ_ok_mapped_correct list_all_iff)

fun term_ok_mapped ::
  "(name, typ) mapping \<Rightarrow> (name, nat) mapping \<Rightarrow>
    (class \<times> class) set \<Rightarrow> class set \<Rightarrow> term \<Rightarrow> bool" where
  "term_ok_mapped consts arities r f (Fv v T) = typ_ok_mapped arities r f T"
| "term_ok_mapped consts arities r f (Bv n) = True"
| "term_ok_mapped consts arities r f (Ct c T) =
    (case Mapping.lookup consts c of None \<Rightarrow> False
     | Some U \<Rightarrow> typ_ok_mapped arities r f T \<and> tinstT T U)"
| "term_ok_mapped consts arities r f (App t u) =
    (term_ok_mapped consts arities r f t \<and> term_ok_mapped consts arities r f u)"
| "term_ok_mapped consts arities r f (Abs T t) =
    (typ_ok_mapped arities r f T \<and> term_ok_mapped consts arities r f t)"

lemma term_ok_mapped_correct:
  "term_ok_mapped (Mapping.of_alist cto) (Mapping.of_alist tao)
     (set (execlasses sa)) (Field (set (execlasses sa))) t =
   exeterm_ok' (ExeSignature cto tao sa) t"
  by (induction t)
    (simp_all add: typ_ok_mapped_correct typ_ok_prepared_correct[symmetric]
      Mapping.lookup_of_alist lookup_eq_map_of_ap split: option.splits)

definition axiom_terms_mapped ::
  "(name, typ) mapping \<Rightarrow> (name, nat) mapping \<Rightarrow>
    (class \<times> class) set \<Rightarrow> class set \<Rightarrow> term list \<Rightarrow> bool" where
  "axiom_terms_mapped consts arities r f ax =
    list_all (\<lambda>p. term_ok_mapped consts arities r f p \<and> typ_of p = Some propT) ax"

definition axiom_terms_relation ::
  "(name \<times> typ) list \<Rightarrow> (name \<times> nat) list \<Rightarrow>
    (class \<times> class) set \<Rightarrow> term list \<Rightarrow> bool" where
  "axiom_terms_relation cto tao r ax =
    axiom_terms_mapped (Mapping.of_alist cto) (Mapping.of_alist tao) r (Field r) ax"

lemma axiom_terms_relation_correct:
  "axiom_terms_relation cto tao (set (execlasses sa)) ax =
    (\<forall>p \<in> set ax. exeterm_ok' (ExeSignature cto tao sa) p \<and> typ_of p = Some propT)"
  by (simp add: axiom_terms_relation_def axiom_terms_mapped_def
    term_ok_mapped_correct list_all_iff)

definition required_eq_axioms :: "term list \<Rightarrow> bool" where
  "required_eq_axioms ax = list_all (List.member ax)
    [eq_reflexive_ax, eq_symmetric_ax, eq_transitive_ax, eq_intr_ax,
     eq_elim_ax, eq_combination_ax, eq_abstract_rule_ax]"

lemma required_eq_axioms_correct:
  "required_eq_axioms ax = (eq_axs \<subseteq> set ax)"
  by (auto simp add: required_eq_axioms_def)

declare [[code drop: exe_wf_theory]]
lemma wf_theory_indexed_code[code]:
  "exe_wf_theory (ExeTheory (ExeSignature cto tao sa) ax) =
    (exe_sig_conds (ExeSignature cto tao sa) \<and>
     axiom_terms_relation cto tao (set (execlasses sa)) ax \<and>
     exeis_std_sig (ExeSignature cto tao sa) \<and>
     exe_wf_sig (ExeSignature cto tao sa) \<and> required_eq_axioms ax)"
  by (simp only: exe_wf_theory_code exe_wf_theory'.simps
    axiom_terms_relation_correct required_eq_axioms_correct)

text \<open>Index successors instead of comparing unrelated pairs of edges.\<close>

fun successor_map :: "('a \<times> 'a) list \<Rightarrow> ('a, 'a set) mapping" where
  "successor_map [] = Mapping.empty"
| "successor_map ((x, y) # cs) =
    (let m = successor_map cs in
      Mapping.update x (insert y (the_default {} (Mapping.lookup m x))) m)"

lemma successor_map_correct:
  "the_default {} (Mapping.lookup (successor_map cs) x) = {y. (x, y) \<in> set cs}"
  by (induction cs)
    (auto simp add: Let_def Mapping.lookup_update' split: prod.splits if_splits option.splits)

definition trans_successors :: "('a, 'a set) mapping \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool" where
  "trans_successors m cs = list_all (\<lambda>(x, y).
    the_default {} (Mapping.lookup m y) \<subseteq> the_default {} (Mapping.lookup m x)) cs"

lemma trans_successors_correct:
  "trans_successors (successor_map cs) cs = trans (set cs)"
  by (auto simp add: trans_successors_def successor_map_correct list_all_iff trans_def)

definition subclass_sets :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "subclass_sets cs r =
    (trans_successors (successor_map cs) cs \<and>
     (\<forall>(x,y) \<in> r. (y,x) \<in> r \<longrightarrow> x = y) \<and>
     (\<forall>x \<in> Field r. (x,x) \<in> r))"

declare [[code drop: exe_wf_subclass]]
lemma subclass_indexed_code[code]:
  "exe_wf_subclass cs = subclass_sets cs (set cs)"
  by (auto simp add: exe_wf_subclass_def subclass_sets_def trans_successors_correct
    antisym_iff_exe_antisym[symmetric] antisym_def refl_on_def intro: FieldI1 FieldI2)

text \<open>Instantiate each axiom proposition once before closing its variables.\<close>

definition close_axiom :: "term \<Rightarrow> term" where
  "close_axiom t = forall_intro_vars t []"

text \<open>Reuse the same lookup maps and sort relation throughout proof replay.\<close>

definition mapped_tcs ::
  "(name \<times> (class \<times> sort list) list) list \<Rightarrow>
    (name, (class, sort list) mapping) mapping" where
  "mapped_tcs tcs = Mapping.map_values (\<lambda>_. Mapping.of_alist) (Mapping.of_alist tcs)"

fun has_sort_mapped ::
  "(class \<times> class) set \<Rightarrow> (name, (class, sort list) mapping) mapping \<Rightarrow>
    typ \<Rightarrow> sort \<Rightarrow> bool" where
  "has_sort_mapped r tcs (Tv v S) S' = sort_leq r S S'"
| "has_sort_mapped r tcs (Ty a Ts) S =
    (case Mapping.lookup tcs a of None \<Rightarrow> False
     | Some mgd \<Rightarrow> (\<forall>C \<in> S.
       case Mapping.lookup mgd C of None \<Rightarrow> False
       | Some Ss \<Rightarrow> list_all2 (has_sort_mapped r tcs) Ts Ss))"

lemma has_sort_mapped_correct:
  "has_sort_mapped (set (execlasses sa)) (mapped_tcs (exetcsigs sa)) T S = exehas_sort sa T S"
  by (induction T arbitrary: S)
    (auto simp add: mapped_tcs_def Mapping.lookup_map_values Mapping.lookup_of_alist
      lookup_eq_map_of_ap exesort_les_code[symmetric] list_all2_conv_all_nth
      split: option.splits)

lemma typ_ok_signature_mapped:
  "typ_ok_mapped (Mapping.of_alist tao) (set (execlasses sa))
      (Field (set (execlasses sa))) T = exetyp_ok_sig (ExeSignature cto tao sa) T"
  using typ_ok_prepared_correct[of "ExeSignature cto tao sa" T]
  by (simp add: typ_ok_mapped_correct)

definition term_closed_mapped ::
  "(name, typ) mapping \<Rightarrow> (name, nat) mapping \<Rightarrow>
    (class \<times> class) set \<Rightarrow> class set \<Rightarrow> term \<Rightarrow> bool" where
  "term_closed_mapped consts arities r f t =
    (term_ok_mapped consts arities r f t \<and> typ_of t \<noteq> None)"

lemma term_closed_mapped_correct:
  "term_closed_mapped (Mapping.of_alist cto) (Mapping.of_alist tao)
     (set (execlasses sa)) (Field (set (execlasses sa))) t =
   exeterm_ok (ExeTheory (ExeSignature cto tao sa) ax) t"
  by (simp add: term_closed_mapped_def term_ok_mapped_correct)

definition inst_ok_mapped ::
  "(name, nat) mapping \<Rightarrow> (class \<times> class) set \<Rightarrow> class set \<Rightarrow>
    (name, (class, sort list) mapping) mapping \<Rightarrow> tyinst list \<Rightarrow> bool" where
  "inst_ok_mapped arities r f tcs insts =
    (distinct (map fst insts) \<and> list_all (typ_ok_mapped arities r f) (map snd insts) \<and>
     list_all (\<lambda>((idn, S), T). has_sort_mapped r tcs T S) insts)"

lemma inst_ok_mapped_correct:
  "inst_ok_mapped (Mapping.of_alist tao) (set (execlasses sa))
      (Field (set (execlasses sa))) (mapped_tcs (exetcsigs sa)) insts =
    exeinst_ok (ExeTheory (ExeSignature cto tao sa) ax) insts"
  by (simp add: inst_ok_mapped_def typ_ok_mapped_correct
    typ_ok_prepared_correct[symmetric] has_sort_mapped_correct list_all_iff)


fun replay_mapped ::
  "(name, typ) mapping \<Rightarrow> (name, nat) mapping \<Rightarrow>
    (class \<times> class) set \<Rightarrow> class set \<Rightarrow>
    (name, (class, sort list) mapping) mapping \<Rightarrow> term list \<Rightarrow>
    (variable \<times> typ) list \<Rightarrow> variable set \<Rightarrow>
    term list \<Rightarrow> proofterm \<Rightarrow> term option" where
  "replay_mapped consts arities r f tcs ax _ _ Hs (PAxm t Tis) = (if inst_ok_mapped arities r f tcs Tis \<and> term_closed_mapped consts arities r f t
    then if t \<in> set ax
      then Some (close_axiom (subst_typ' Tis t)) 
    else None else None)"
| "replay_mapped consts arities r f tcs ax _ _ Hs (PBound n) = partial_nth Hs n" 
| "replay_mapped consts arities r f tcs ax vs ns Hs (Abst T p) = (if typ_ok_mapped arities r f T 
    then (let (s',ns') = variant_variable (Free STR ''default'') ns in 
      map_option (mk_all s' T) (replay_mapped consts arities r f tcs ax ((s', T) # vs) ns' Hs p))
    else None)"
| "replay_mapped consts arities r f tcs ax vs ns Hs (Appt p t) = 
    (let rep = replay_mapped consts arities r f tcs ax vs ns Hs p in
    let t' = subst_bvs (map (\<lambda>(x,y) . Fv x y) vs) t in
      case (rep, typ_of t') of
        (Some (Ct s (Ty fun1 [Ty fun2 [\<tau>, Ty propT1 Nil], Ty propT2 Nil]) $ b), Some \<tau>') \<Rightarrow> 
          if s = STR ''Pure.all'' \<and> fun1 = STR ''fun'' \<and> fun2 = STR ''fun'' 
            \<and> propT1 = STR ''prop'' \<and> propT2 = STR ''prop''
             \<and> \<tau>=\<tau>' \<and> term_closed_mapped consts arities r f t'
            then Some (b \<bullet> t') else None
      | _ \<Rightarrow> None)" 
| "replay_mapped consts arities r f tcs ax vs ns Hs (AbsP t p) =
    (let t' = subst_bvs (map (\<lambda>(x,y) . Fv x y) vs) t in
    let rep = replay_mapped consts arities r f tcs ax vs ns (t'#Hs) p in
      (if typ_of t' = Some propT \<and> term_closed_mapped consts arities r f t' then map_option (mk_imp t') rep else None))"
| "replay_mapped consts arities r f tcs ax vs ns Hs (AppP p1 p2) = 
    (let rep1 = Option.bind (replay_mapped consts arities r f tcs ax vs ns Hs p1) beta_eta_norm in
    let rep2 = Option.bind (replay_mapped consts arities r f tcs ax vs ns Hs p2) beta_eta_norm in
      (case (rep1, rep2) of (
        Some (Ct imp (Ty fn1 [Ty prp1 [], Ty fn2 [Ty prp2 [], Ty prp3 []]]) $ A $ B),
        Some A') \<Rightarrow> 
          if imp = STR ''Pure.imp'' \<and> fn1 = STR ''fun'' \<and> fn2 = STR ''fun''
            \<and> prp1 = STR ''prop'' \<and> prp2 = STR ''prop'' \<and> prp3 = STR ''prop'' \<and> A=A' 
          then Some B else None
        | _ \<Rightarrow> None))"
| "replay_mapped consts arities r f tcs ax vs ns Hs (OfClass ty c) = (if has_sort_mapped r tcs ty {c} 
    \<and> typ_ok_mapped arities r f ty
    then (case Mapping.lookup consts (const_of_class c) of 
      Some (Ty fun [Ty it [ity], Ty prop []]) \<Rightarrow> 
        if ity = tvariable STR '''a'' \<and> fun = STR ''fun'' \<and> prop = STR ''prop'' \<and> it = STR ''itself''
          then Some (mk_of_class ty c) else None | _ \<Rightarrow> None) else None)"
| "replay_mapped consts arities r f tcs ax vs ns Hs (Hyp t) = (if t\<in>set Hs then Some t else None)"

lemma replay_mapped_correct:
  "replay_mapped (Mapping.of_alist cto) (Mapping.of_alist tao)
     (set (execlasses sa)) (Field (set (execlasses sa)))
     (mapped_tcs (exetcsigs sa)) ax vs ns Hs P =
   exereplay' (ExeTheory (ExeSignature cto tao sa) ax) vs ns Hs P"
  by (induction P arbitrary: vs ns Hs)
    (simp_all add: inst_ok_mapped_def term_closed_mapped_def
      typ_ok_mapped_correct typ_ok_prepared_correct[symmetric]
      term_ok_mapped_correct has_sort_mapped_correct
      Mapping.lookup_of_alist lookup_eq_map_of_ap close_axiom_def list_all_iff Let_def
      cong: option.case_cong term.case_cong typ.case_cong list.case_cong)

definition replay_tables ::
  "(name, typ) mapping \<Rightarrow> (name, nat) mapping \<Rightarrow>
    (class \<times> class) set \<Rightarrow> class set \<Rightarrow>
    (name, (class, sort list) mapping) mapping \<Rightarrow>
    term list \<Rightarrow> proofterm \<Rightarrow> term option" where
  "replay_tables consts arities r f tcs ax P =
    (if \<forall>x \<in> set (hyps P).
        term_closed_mapped consts arities r f x \<and> typ_of x = Some propT
     then Option.bind (replay_mapped consts arities r f tcs ax []
       (fst ` (fv_Proof P \<union> FV (set (hyps P)))) (hyps P) P) beta_eta_norm
     else None)"

definition replay_relation ::
  "(name \<times> typ) list \<Rightarrow> (name \<times> nat) list \<Rightarrow> exeosig \<Rightarrow>
    (class \<times> class) set \<Rightarrow> term list \<Rightarrow> proofterm \<Rightarrow> term option" where
  "replay_relation cto tao sa r ax P =
    replay_tables (Mapping.of_alist cto) (Mapping.of_alist tao) r (Field r)
      (mapped_tcs (exetcsigs sa)) ax P"

declare [[code drop: exereplay]]
lemma replay_indexed_code[code]:
  "exereplay (ExeTheory (ExeSignature cto tao sa) ax) P =
    replay_relation cto tao sa (set (execlasses sa)) ax P"
  by (simp add: exereplay_def replay_relation_def replay_tables_def
    replay_mapped_correct term_closed_mapped_def term_ok_mapped_correct)


text \<open>Optimized Export\<close>

export_code exereplay exe_wf_theory
  Bv PBound Tv Free ExeTheory ExeSignature
  int nat sort exenormalize_sort eq_term
  in SML module_name ExportCheck file_prefix export

end

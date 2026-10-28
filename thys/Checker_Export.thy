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


text \<open>Optimized Export\<close>

export_code exereplay exe_wf_theory
  Bv PBound Tv Free ExeTheory ExeSignature
  int nat sort exenormalize_sort eq_term
  in SML module_name ExportCheck file_prefix export

end

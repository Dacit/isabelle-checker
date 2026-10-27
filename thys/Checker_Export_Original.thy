theory Checker_Export_Original
  imports Metalogic_ProofChecker.CodeGen
begin

text \<open>Constants for Interface\<close>

definition sort :: "String.literal list \<Rightarrow> sort" where
  "sort xs = set xs"

definition eq_typ :: "typ \<Rightarrow> typ \<Rightarrow> bool" where
  "eq_typ a b \<longleftrightarrow> a = b"

definition eq_term :: "term \<Rightarrow> term \<Rightarrow> bool" where
  "eq_term a b \<longleftrightarrow> a = b"

definition eq_var :: "variable \<Rightarrow> variable \<Rightarrow> bool" where
  "eq_var a b \<longleftrightarrow> a = b"

definition norm :: "term \<Rightarrow> term option" where
  "norm t = map_option eta_norm (beta_norm t)"

definition vars :: "term \<Rightarrow> (variable \<times> typ) list" where
  "vars t = rev (add_vars' t [])"

definition of_class :: "typ \<Rightarrow> class \<Rightarrow> term" where
  "of_class t c = mk_of_class t c"

definition term_ok :: "exesignature \<Rightarrow> term \<Rightarrow> bool" where
  "term_ok s t = exeterm_ok' s t"

definition type_of :: "term \<Rightarrow> typ option" where
  "type_of t = typ_of t"

definition int :: "integer \<Rightarrow> int" where
  "int n = int_of_integer n"

definition nat :: "integer \<Rightarrow> nat" where
  "nat n = nat_of_integer n"

section \<open>Normal export\<close>

export_code exe_check_proof exereplay exe_wf_theory exe_wf_sig exe_sig_conds exeis_std_sig sort
  eq_typ eq_term eq_var norm vars of_class term_ok type_of int nat Bv PBound Tv Free ExeTheory
  ExeSignature
  in SML module_name ExportCheck file_prefix export

end
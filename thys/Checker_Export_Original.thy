theory Checker_Export_Original
  imports Metalogic_ProofChecker.CodeGen
begin

text \<open>Constants for better Interface\<close>

definition int :: "integer \<Rightarrow> int" where
  "int n = int_of_integer n"

definition nat :: "integer \<Rightarrow> nat" where
  "nat n = nat_of_integer n"

definition sort :: "String.literal list \<Rightarrow> sort" where
  "sort xs = set xs"


section \<open>Normal export (+ constants)\<close>

export_code exe_check_proof exereplay exe_wf_theory
  Bv PBound Tv Free ExeTheory ExeSignature
  int nat sort exenormalize_sort
  in SML module_name ExportCheck file_prefix export

end
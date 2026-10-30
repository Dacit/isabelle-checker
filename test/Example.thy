\<^marker>\<open>author Fabian Huch\<close>
theory Example
  imports Main Proof_Checker
  options[record_proofs = 2] \<comment> \<open>also build HOL with \<open>-o record_proofs=2\<close>\<close>
begin

lemma t: "1 + (1::nat) = 2" by simp

definition allp :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> bool" where
  "allp f P \<equiv> \<forall>x. P (f x)"

lemma example1: "allp (\<lambda>x::'a. c) P \<longleftrightarrow> P c"
  by (metis allp_def)

lemma example2: "allp (\<lambda>x::'a. c) P \<longleftrightarrow> P c"
  by (metis allp_def)

check_theory

end

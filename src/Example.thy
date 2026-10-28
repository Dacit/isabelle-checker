theory Example
  imports Main Check_Build
  options[record_proofs = 2]
begin

lemma t: "1 + (1::nat) = 2" by simp

check_theory

end

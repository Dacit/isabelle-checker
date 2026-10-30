theory Bad
  imports Main
begin

lemma flex_rule1: "x True \<Longrightarrow> x True" . \<comment>\<open>Important: x here and below must share the same name.\<close>
lemma flex_rule2: "P True \<Longrightarrow> \<forall>x::bool. P True" by simp

lemma bad: "\<forall>y::bool. False" \<comment> \<open>Important: name of y must not be equal to x\<close>
  apply (rule flex_rule1[THEN flex_rule2])
  by (rule TrueI) 

end
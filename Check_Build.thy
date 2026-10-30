\<^marker>\<open>author Fabian Huch\<close>
theory Check_Build
  imports Proof_Checker
begin

ML \<open>
val _ =
  check_build
    (space_explode "," (Options.default_string \<^system_option>\<open>trusted_theories\<close>))
\<close>

end
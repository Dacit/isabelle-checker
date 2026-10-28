\<^marker>\<open>author Fabian Huch\<close>
theory Check_Build
  imports Pure
  keywords "check_theory" :: diag
begin

ML_file \<open>set_export.ML\<close>
ML_file \<open>checker.ML\<close>

ML \<open>
fun check_thmss trusted ax0 seen0 thmss thy =
  let
    val (theory as (sign, ax)) = Checker.theory_of thy
    val ax1 = ax0 @ ax
    val _ = if Checker.wf_theory theory then () else error "Theory not well-formed"

    val seen = Unsynchronized.ref seen0

    fun check_proof name t p =
      let
        fun check_pthm (thm_header as {prop, types, thm_name, theory_name, ...}, thm_body) =
          let
            val serial = #serial (Proofterm.thm_header_id thm_header)
            val Tinst = the types |> map Checker.typ
          in
            case Inttab.lookup (!seen) serial of
               SOME (_, (t1, Ts)) => Checker.PAxm (t1, Ts ~~ Tinst)
             | NONE =>
                let
                  val (name1, (t1, Ts)) =
                    if Symtab.defined trusted theory_name 
                    then ("", (Checker.term prop, Checker.tvars_of prop))
                    else
                      Proofterm.thm_body_proof_open thm_body
                      |> Proofterm.reconstruct_proof thy prop
                      |> check_proof (Thm_Name.print_pos thm_name) prop
                  val _ = Unsynchronized.change seen (Inttab.update (serial, (name1, (t1, Ts))))
                in Checker.PAxm (t1, Ts ~~ Tinst) end
          end

      val proofterm = Checker.proofterm check_pthm p
      val ax2 = Inttab.dest (!seen) |> map (fst o snd o snd)
      val _ =
        if Checker.wf_theory_proof (sign, ax1 @ ax2) proofterm (Checker.term t) then ()
        else error ("Incorrect proof term in " ^ name)
    in (name, (Checker.term t, Checker.tvars_of t)) end

    fun check_thm thm_name thm =
      let
        val thm1 = thm |> Thm.transfer thy |> Thm.unconstrainT
        val prf = (Thm.reconstruct_proof_of thm1)
        val (name, (t, Ts)) = check_proof (Thm_Name.print thm_name) (Thm.full_prop_of thm1) prf
      in (name, (t, Ts)) end

    fun check_thms (name, thms) = map_index (fn (i, thm) => check_thm (name, i) thm) thms
    val checked = maps check_thms thmss
  in (checked, !seen) end

fun check_current thy =
  let
    val trusted =
      Theory.ancestors_of thy |> map (rpair () o Context.theory_long_name) |> Symtab.make
    val parent_facts = Theory.parents_of thy |> map Global_Theory.facts_of
    val thmss = Global_Theory.facts_of thy |> Facts.dest_static true parent_facts
    val (checked, _) = check_thmss trusted [] Inttab.empty thmss thy
  in checked |> map fst |> filter_out (equal "") end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>check_theory\<close> "check proof terms"
    (Scan.succeed
      (Toplevel.keep (fn st =>
        let
          val thy = Toplevel.theory_of st
          val checked = check_current thy
        in checked |> map Pretty.str |> Pretty.chunks |> Pretty.writeln end)))
\<close>

end

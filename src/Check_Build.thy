theory Check_Build
  imports Main
begin

ML_file \<open>set_export.ML\<close>
ML_file \<open>checker.ML\<close>

ML \<open>
fun check_thy (thy: theory) trusted_thys =
  let
    val (theory0 as (sign, ax0)) = Checker.theory_of thy
    val _ = if Checker.wf_theory theory0 then () else error "Theory not well-formed"

    val seen = Unsynchronized.ref Inttab.empty

    fun check_proof name t p =
      let
        fun check_pthm (thm_header as {prop, types, theory_name, ...}, thm_body) =
          let
            val serial = #serial (Proofterm.thm_header_id thm_header)
            val Tinst = the types |> map Checker.typ
          in
            case Inttab.lookup (!seen) serial of
               SOME (t1, Ts) => Checker.PAxm (t1, Ts ~~ Tinst)
             | NONE =>
                let
                  val _ =
                    if Symtab.defined trusted_thys theory_name then ()
                    else
                      Proofterm.thm_body_proof_open thm_body
                      |> Proofterm.reconstruct_proof thy prop
                      |> check_proof name prop
                  val t1 = Checker.term prop
                  val Ts = Checker.tvars_of prop
                  val _ = Unsynchronized.change seen (Inttab.update (serial, (t1, Ts)))
                in Checker.PAxm (t1, Ts ~~ Tinst) end
          end

      val proofterm = Checker.proofterm check_pthm p
      val ax1 = Inttab.dest (!seen) |> map (fst o snd)
      val ok = Checker.check_proof (sign, ax0 @ ax1) proofterm (Checker.term t)
    in if ok then () else error ("Incorrect proof term in " ^ name) end

    fun check_thm name thm =
      let
        val thm1 = thm |> Thm.transfer thy |> Thm.unconstrainT
      in check_proof name (Thm.full_prop_of thm1) (Thm.reconstruct_proof_of thm1) end
    fun check_thms (name, thms) = (app (check_thm name) thms; writeln ("Checked " ^ name))

    val parent_facts = Theory.parents_of thy |> map Global_Theory.facts_of
    val thmss = Global_Theory.facts_of thy |> Facts.dest_static true parent_facts
  in app check_thms thmss end

fun check_current thy =
  let
    val trusted =
      Theory.ancestors_of thy |> map (rpair () o Context.theory_long_name) |> Symtab.make
  in check_thy thy trusted end
\<close>

end
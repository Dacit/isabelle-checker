\<^marker>\<open>author Fabian Huch\<close>
theory Proof_Checker
  imports Pure
  keywords "check_theory" :: diag
begin

ML_file \<open>checker_export.ML\<close>
ML_file \<open>checker.ML\<close>

ML \<open>
fun lazy_default opt f = case opt of SOME e => e | NONE => f ()
fun check opt msg = lazy_default opt (fn () => error msg)

fun cache table_ref serial value =
  (Unsynchronized.change table_ref (Inttab.update (serial, value)); value)

fun cached table_ref f serial =
  lazy_default (Inttab.lookup (!table_ref) serial) ((cache table_ref serial) o f)

fun check_thmss trusted (checked0, seen0) thmss cthy =
  let
    val seen = Unsynchronized.ref seen0

    fun check_proof name thm =
      let
        val proof_seen = Unsynchronized.ref Inttab.empty

        fun lookup_global f serial = snd (cached seen f serial)
        fun lookup f serial = cached proof_seen (fn () => lookup_global f serial) serial

        fun checked_pthm_axm (pthm as (header as {thm_name, theory_name, ...}, _)) =
          let
            val serial = #serial (Proofterm.thm_header_id header)
            fun check_pthm () =
              if Symtab.defined trusted theory_name then ("", Checker.axiomatize pthm)
              else check_proof (Thm_Name.print_pos thm_name) (Checker.pthm cthy pthm)
          in lookup check_pthm serial end

        val prf = Checker.proof checked_pthm_axm thm
        val cthm =
          check
            (Checker.check cthy (Inttab.dest (!proof_seen) |> map snd) thm prf) 
            ("Incorrect proof term for " ^ name)
      in (name, cthm) end

    fun check_thm thm_name thm =
      let
        val (name, cthm) = check_proof (Thm_Name.print thm_name) (Checker.thm cthy thm)
        val _ = writeln ("Checked " ^ name)
      in (name, cthm) end

    fun check_thms (name, thms) = map_index (fn (i, thm) => check_thm (name, i) thm) thms
    val checked = maps check_thms thmss

  in (checked0 @ checked, !seen) end

fun check_thy thy = check (Checker.cthy thy) "Invalid theory signature"

fun check_current thy =
  let
    val trusted =
      Theory.ancestors_of thy |> map (rpair () o Context.theory_long_name) |> Symtab.make
    val parent_facts = Theory.parents_of thy |> map Global_Theory.facts_of
    val thmss = Global_Theory.facts_of thy |> Facts.dest_static true parent_facts
  in check_thmss trusted ([], Inttab.empty) thmss (check_thy thy) end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>check_theory\<close> "check proof terms"
    (Scan.succeed
      (Toplevel.keep (fn st =>
        let
          val thy = Toplevel.theory_of st
          val (checked, seen) = check_current thy
          val msg =
            "Checked " ^ (checked |> length |> string_of_int) ^ " thms with " ^ 
              (seen |> Inttab.size |> string_of_int) ^ " intermediate thms"
        in writeln msg end)))

fun check_build trusted_theories =
  let
    val trusted = Symtab.make (map (rpair ()) trusted_theories)

    fun check_step thy ((prev_thys, prev_cthy), results0) =
      let
        val thmss =
          Facts.dest_static true (map Global_Theory.facts_of prev_thys) (Global_Theory.facts_of thy)
      in 
        if null thmss then (([thy], prev_cthy), results0)
        else
          let
            val cthy =
              case Checker.cthy_map prev_cthy thy of SOME cthy => cthy | NONE => check_thy thy
          in (([thy], SOME cthy), check_thmss trusted results0 thmss cthy) end
      end

    fun check_theory theory_name theories_seen =
      let
        val thy = Build.get_theory theory_name
        val parents = Theory.parents_of thy
        val parents_seen =
          parents 
          |> map_filter ((Symtab.lookup theories_seen) o Context.theory_long_name)
          |> Inttab.joins (K fst)
        val thys =
          Build.get_theory_segments theory_name
          |> map #state |> filter Toplevel.is_theory |> map Toplevel.theory_of
        val ((_, last_cthy), (checked, seen)) =
          fold check_step (thys @ [thy]) ((parents, Checker.cthy thy), ([], parents_seen))
        val _ = check (Checker.cthy_map last_cthy thy) "Invalid theory signature"
        val _ = \<^scala>\<open>check_result\<close> (theory_name :: map fst checked)
      in Symtab.update (theory_name, seen) theories_seen end

    val _ = 
      Build.all_theories ()
      |> filter_out (Symtab.defined trusted)
      |> fold check_theory |> Symtab.build
  in () end
\<close>

end

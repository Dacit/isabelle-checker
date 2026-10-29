\<^marker>\<open>author Fabian Huch\<close>
theory Proof_Checker
  imports Pure
  keywords "check_theory" :: diag
begin

ML \<open>open Context\<close>

ML_file \<open>checker_export.ML\<close>
ML_file \<open>checker.ML\<close>

ML \<open>
fun check_thmss trusted (checked0, seen0) thmss cthy =
  let
    val seen = Unsynchronized.ref seen0

    fun check_proof name thm =
      let
        fun checked_pthm_axm (pthm as (header as {thm_name, theory_name, ...}, _)) =
          let val serial = #serial (Proofterm.thm_header_id header)
          in
            case Inttab.lookup (!seen) serial of
              SOME (_, cthm) => cthm
            | NONE =>
              let
                val (name1, cthm) =
                  if Symtab.defined trusted theory_name then ("", Checker.axiomatize pthm)
                  else check_proof (Thm_Name.print_pos thm_name) (Checker.pthm cthy pthm)
                val _ = Unsynchronized.change seen (Inttab.update (serial, (name1, cthm)))
              in cthm end
          end

        val prf = Checker.proof checked_pthm_axm thm
        val cthms = (checked0 @ (Inttab.dest (!seen) |> map snd)) |> map snd
        val cthm =
          case Checker.check cthy cthms thm prf of
            SOME cthm => cthm 
          | NONE => error ("Incorrect proof term for " ^ name)
        val _ = writeln ("Checked " ^ name)
      in (name, cthm) end

    fun check_thm thm_name thm = check_proof (Thm_Name.print thm_name) (Checker.thm cthy thm)
    fun check_thms (name, thms) = map_index (fn (i, thm) => check_thm (name, i) thm) thms
    val checked = maps check_thms thmss

  in (checked, !seen) end

fun check_thy thy = case Checker.cthy thy of NONE => error "Invalid theory" | SOME cthy => cthy

fun check_current thy =
  let
    val trusted =
      Theory.ancestors_of thy |> map (rpair () o Context.theory_long_name) |> Symtab.make
    val parent_facts = Theory.parents_of thy |> map Global_Theory.facts_of
    val thmss = Global_Theory.facts_of thy |> Facts.dest_static true parent_facts
    val (checked, _) = check_thmss trusted ([], Inttab.empty) thmss (check_thy thy)
  in checked |> map fst |> filter_out (equal "") end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>check_theory\<close> "check proof terms"
    (Scan.succeed
      (Toplevel.keep (fn st =>
        let
          val thy = Toplevel.theory_of st
          val num = length (check_current thy)
        in writeln ("Checked " ^ (string_of_int num) ^ " thms") end)))

fun check_theory theory_name trusted_theories =
  let
    val trusted = Symtab.make trusted_theories
    fun check_segment (st, ((prev_thys, prev_cthy), results0)) =
      let 
        val thy = Toplevel.theory_of st
        val cthy = case Checker.cthy_map prev_cthy thy of SOME cthy => cthy | NONE => check_thy thy
        val thmss =
          Facts.dest_static true (map Global_Theory.facts_of prev_thys) (Global_Theory.facts_of thy)
        val result1 = if null thmss then results0 else check_thmss trusted results0 thmss cthy
      in (([thy], SOME cthy), result1) end

    val init = ([], Inttab.empty)

    fun check_states states =
      if null states then (([], NONE), init)
      else
        let
          val thy = Toplevel.theory_of (hd states)
          val parents = Theory.parents_of thy
        in List.foldl check_segment ((parents, Checker.cthy thy), init) states end

    val states = Build.get_theory_segments theory_name |> map #state |> filter Toplevel.is_theory
    val (_, (checked, seen)) = check_states states
    val checked1 = Inttab.dest seen |> map (fst o snd) |> filter_out (equal "")
  in map fst checked @ checked1 end
\<close>

end

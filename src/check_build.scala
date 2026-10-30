/*  Title:      check_build.scala
    Author:     Fabian Huch

Command-line tools to build and check proofterms of Isabelle sessions.
*/

package isabelle

import scala.collection.mutable


object Check_Build {
  def home_dir: Path = Path.explode("$ISABELLE_CHECKER_HOME")


  /* results */

  final case class Result(thms: List[String], ok: Boolean) {
    def rc: Int = if (ok) 0 else 1
  }

  object Results {
    def apply(build: Build.Results, sessions: List[(String, Result)]): Results =
      new Results(build, sessions.toMap)
  }

  final class Results private(val build: Build.Results, val sessions: Map[String, Result]) {
    def sessions_ok: Boolean = sessions.values.forall(_.ok)
    def rc: Int = if (!build.ok) build.rc else if (sessions_ok) 0 else 1
  }


  /* scala function */

  private val theory_results = Synchronized(Map.empty[String, List[String]])

  object Check_Result extends Scala.Fun_Strings("check_result") {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = {
      val (theory_name, checked_thms) =
        args match {
          case theory_name :: checked_thms => (theory_name, checked_thms)
          case Nil => error("Malformed arguments")
        }
      theory_results.change(_ + (theory_name -> checked_thms))
      Nil
    }
  }


  /* check */

  def check_session(
    options: Options,
    background: Sessions.Background,
    check_theories: List[Document.Node.Name],
    trusted_theories: List[Document.Node.Name] = Nil,
    dirs: List[Path] = Nil,
    augment_options: String => Options.Update = _ => Nil,
    cache: Rich_Text.Cache = Rich_Text.Cache.make(),
    progress: Progress = new Progress
  ): Result =
    Isabelle_System.with_tmp_dir("private") { private_dir =>
      val session = background.session_name
      progress.echo("Checking " + session + " ...")

      theory_results.change(_ => Map.empty)

      val options1 =
        options + Options.Spec.eq("trusted_theories", trusted_theories.map(_.theory).mkString(","))

      val session_entry =
        Sessions.Session_Entry(
          parent = Some(session),
          imports = List("Proof_Checker"),
          theories = List((Nil, List((("Check_Build", Position.none), false)))))

      val session_info =
        Sessions.Info.make(session_entry, draft_session = true, dir = home_dir, options = options1)

      def session_setup(setup_session_name: String, session: Session): Unit = {
        if (setup_session_name == Sessions.DRAFT) {
          session.all_messages += Session.Consumer[Prover.Message]("check_build") {
            case output: Prover.Output
              if Protocol.is_exported(output.message) || Protocol.is_state(output.message) =>
              output.properties match {
                case Position.Line_File(line, file) =>
                  val pos = Position.Line_File(line, file)
                  if (Build.print_log_check(pos, output.message, Nil, Nil)) {
                    progress.echo(Protocol.message_text(output.message, pos = pos), verbose = true)
                  }
                case _ =>
              }
            case _ =>
          }
        }
      }

      val res =
        Build.build(options, private_dir = Some(private_dir), dirs = home_dir.absolute :: dirs,
          infos = List(session_info), augment_options = augment_options, selection =
          Sessions.Selection.session(Sessions.DRAFT), session_setup = session_setup, cache = cache)

      val thy_results = check_theories.map(node => theory_results.value.get(node.theory))
      val result = Result(thy_results.flatten.flatten, res.ok && thy_results.forall(_.isDefined))

      if (result.ok) progress.echo("Checked " + result.thms.length + " proofs in " + session)
      else progress.echo_error_message("Found incorrect proof term in " + session)

      result
    }

  def check_build(
    options: Options,
    selection: Sessions.Selection = Sessions.Selection.empty,
    trusted_sessions: List[String] = Nil,
    browser_info: Browser_Info.Config = Browser_Info.Config.none,
    progress: Progress = new Progress,
    check_unknown_files: Boolean = false,
    clean_build: Boolean = false,
    afp_root: Option[Path] = None,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Option[Int] = None,
    fresh_build: Boolean = false,
    export_files: Boolean = false,
    cache: Rich_Text.Cache = Rich_Text.Cache.make()
  ): Results = {
    val all_dirs = select_dirs ::: dirs ::: AFP.main_dirs(afp_root)
    val full_sessions_structure = Sessions.load_structure(options, dirs = all_dirs)

    full_sessions_structure.check_sessions(trusted_sessions)
    val all_trusted_sessions = full_sessions_structure.build_requirements(trusted_sessions)
    val is_trusted = all_trusted_sessions.toSet

    def augment_options(session: String): Options.Update =
      Options.Spec.eq("record_proofs", "2") ::
        (if (is_trusted(session)) Nil else List(Options.Spec.make("record_theories")))

    val build_result =
      Build.build(options, selection = selection, browser_info = browser_info, progress = progress,
        check_unknown_files = check_unknown_files, build_heap = true, clean_build = clean_build,
        afp_root = afp_root, dirs = dirs, select_dirs = select_dirs, numa_shuffling =
        numa_shuffling, max_jobs = max_jobs, fresh_build = fresh_build, export_files = export_files,
        augment_options = augment_options, cache = cache)

    def all_theories_of(session_name: String): List[Document.Node.Name] = {
      val base = build_result.deps(session_name)
      for (theory_name <- base.loaded_theories.topological_order)
      yield base.known_theories(theory_name).name
    }

    val session_results =
      if (build_result.ok) {
        val trusted_theories = all_trusted_sessions.flatMap(all_theories_of)

        for {
          session <- build_result.deps.sessions_structure.build_graph.maximals
          if build_result.sessions(session)
          if !is_trusted(session)
        } yield session -> {
          val all_theories = all_theories_of(session)
          val (trusted, theories) = all_theories.partition(trusted_theories.contains)

          val infos =
            for (session <- full_sessions_structure.imports_requirements(List(session)))
            yield build_result.info(session)

          val res =
            check_session(options, build_result.deps.background(session), theories,
              trusted_theories = trusted, augment_options = augment_options, dirs = all_dirs,
              cache = cache, progress = progress)

          res
        }
      }
      else Nil

    Results(build_result, session_results)
  }


  /* Isabelle tool wrappers */

  val isabelle_tool =
    Isabelle_Tool("check_build", "build and check proofterms of Isabelle sessions",
      Scala_Project.here,
      { args =>
        var afp_root: Option[Path] = None
        val base_sessions = new mutable.ListBuffer[String]
        val select_dirs = new mutable.ListBuffer[Path]
        var numa_shuffling = false
        var browser_info = Browser_Info.Config.none
        var requirements = false
        val exclude_session_groups = new mutable.ListBuffer[String]
        var all_sessions = false
        var clean_build = false
        val dirs = new mutable.ListBuffer[Path]
        var export_files = false
        var fresh_build = false
        val session_groups = new mutable.ListBuffer[String]
        var max_jobs: Option[Int] = None
        var options = Options.init(update = Options.Spec.ISABELLE_BUILD_OPTIONS)
        var trusted_sessions = new mutable.ListBuffer[String]
        var verbose = false
        val exclude_sessions = new mutable.ListBuffer[String]

        val getopts = Getopts("""
Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -P DIR       enable HTML/PDF presentation in directory (":" for default)
    -R           refer to requirements of selected sessions
    -S           soft build: only observe changes of sources, not heap images
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -c           clean build
    -d DIR       include session directory
    -e           export files from session specification into file-system
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs
                 (default: 1 for local build, 0 for build cluster)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -t NAME      trust session NAME and all requirements
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and check proofterms of Isabelle sessions.

  Notable system settings:
""" + Library.indent_lines(4, Build_Log.Settings.show(ML_Settings(options))) + "\n",
          "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
          "B:" -> (arg => base_sessions += arg),
          "D:" -> (arg => select_dirs += Path.explode(arg)),
          "N" -> (_ => numa_shuffling = true),
          "P:" -> (arg => browser_info = Browser_Info.Config.make(arg)),
          "R" -> (_ => requirements = true),
          "X:" -> (arg => exclude_session_groups += arg),
          "a" -> (_ => all_sessions = true),
          "c" -> (_ => clean_build = true),
          "d:" -> (arg => dirs += Path.explode(arg)),
          "e" -> (_ => export_files = true),
          "f" -> (_ => fresh_build = true),
          "g:" -> (arg => session_groups += arg),
          "j:" -> (arg => max_jobs = Some(Value.Nat.parse(arg))),
          "o:" -> (arg => options = options + arg),
          "t:" -> (arg => trusted_sessions += arg),
          "v" -> (_ => verbose = true),
          "x:" -> (arg => exclude_sessions += arg))

        val sessions = getopts(args)

        val progress =
          new Console_Progress(verbose = verbose,
            threshold = Build.progress_threshold(options),
            detailed = Build.progress_detailed(options))

        val ml_settings = ML_Settings(options)

        progress.echo(
          "Started at " + Build_Log.print_date(progress.start) +
            " (" + ml_settings.ml_identifier + ")",
          verbose = true)
        progress.echo(Build_Log.Settings.show(ml_settings) + "\n", verbose = true)

        val results =
          check_build(options,
            selection = Sessions.Selection(
              requirements = requirements,
              all_sessions = all_sessions,
              base_sessions = base_sessions.toList,
              exclude_session_groups = exclude_session_groups.toList,
              exclude_sessions = exclude_sessions.toList,
              session_groups = session_groups.toList,
              sessions = sessions),
            trusted_sessions = trusted_sessions.toList,
            browser_info = browser_info,
            progress = progress,
            check_unknown_files = Mercurial.is_repository(Path.ISABELLE_HOME),
            clean_build = clean_build,
            afp_root = afp_root,
            dirs = dirs.toList,
            select_dirs = select_dirs.toList,
            numa_shuffling = Host.numa_check(progress, numa_shuffling),
            max_jobs = max_jobs,
            fresh_build = fresh_build,
            export_files = export_files)

        val stop_date = progress.now()
        val elapsed_time = stop_date - progress.start

        progress.echo("\nFinished at " + Build_Log.print_date(stop_date), verbose = true)

        sys.exit(results.rc)
      })
}

class Check_Build_Functions extends Scala.Functions(Check_Build.Check_Result)
class Check_Build_Tools extends Isabelle_Scala_Tools(Check_Build.isabelle_tool)

/*  Title:      check_build.scala
    Author:     Fabian Huch

Command-line tools to build and check proofterms of Isabelle sessions.
*/

package isabelle

import scala.collection.mutable


object Check_Build {
  object Markup_Check_Session_Finished extends isabelle.Markup.Function("check_session_finished")

  final case class Result(thms: List[String] = Nil, finished: Boolean = false) {
    def rc: Int = if (finished) 0 else 1
  }

  object Results {
    def apply(build: Build.Results, sessions: List[(String, Result)]): Results =
      new Results(build, sessions.toMap)
  }

  final class Results private(val build: Build.Results, val sessions: Map[String, Result]) {
    def sessions_ok: Boolean = sessions.values.forall(_.finished)
    def rc: Int = if (!build.ok) build.rc else if (sessions_ok) 0 else 1
  }

  def home_dir: Path = Path.explode("$ISABELLE_CHECKER_HOME")

  def check_session(options: Options,
    background: Sessions.Background,
    theories: List[Document.Node.Name],
    trusted: List[Document.Node.Name] = Nil,
    cache: Rich_Text.Cache = Rich_Text.Cache.make(),
    progress: Progress = new Progress
  ): Result = {
    val store = Store(options, cache = cache)

    val args = {
      import XML.Encode._
      pair(string, pair(list(string), list(string)))(
        (background.session_name, (theories.map(_.theory), trusted.map(_.theory))))
    }

    val env =
      Isabelle_System.Settings.env(List("ISABELLE_CHECKER_ARGS" -> YXML.string_of_body(args)))

    val session =
      new Session {
        def session_options: Options = options
        val interactive = false
        val resources = new Resources(background, background, Logger.none)
      }

    val result = Synchronized(Result())
    session.all_messages += Session.Consumer[Prover.Message]("check_build_output") {
      case msg: Prover.Output =>
        val message = msg.message
        if (msg.is_stdout) progress.echo(Symbol.encode(XML.content(message)))
        if (msg.is_stderr) progress.echo_error_message(Symbol.encode(XML.content(message)))
      case _ =>
    }

    def shutdown(finished: Boolean): Prover.Protocol_Output => Boolean = { _ =>
      result.change { res =>
        val res1 = res.copy(finished = finished)
        session.protocol_command("Prover.stop", XML.Encode.int(res1.rc))
        res1
      }
      true
    }

    session.init_protocol_handler(new Session.Protocol_Handler {
      override val functions: Session.Protocol_Functions =
        List(
          Markup.Build_Session_Finished.name -> shutdown(false),
          Markup_Check_Session_Finished.name -> shutdown(true))
    })

    val process =
      Isabelle_Process.start(options, session, background, store.session_heaps(background),
        cwd = home_dir, env = env)
    Isabelle_Thread.interrupt_handle(process.terminate()) { process.await_shutdown() }

    result.value
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
    infos: List[Sessions.Info] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Option[Int] = None,
    fresh_build: Boolean = false,
    export_files: Boolean = false,
    session_setup: (String, Session) => Unit = (_, _) => (),
    cache: Rich_Text.Cache = Rich_Text.Cache.make()
  ): Results = {
    val sessions_structure =
      Sessions.load_structure(options, dirs = dirs, select_dirs = select_dirs, infos = infos)

    val is_trusted =
      sessions_structure.build_selection(Sessions.Selection(sessions = trusted_sessions)).toSet

    def augment_options(session: String): Options.Update =
      if (is_trusted(session)) Nil else List(Options.Spec.make("record_proofs"))

    val build_result =
      Build.build(options, selection = selection, browser_info = browser_info, progress = progress,
        check_unknown_files = check_unknown_files, build_heap = true, clean_build = clean_build,
        afp_root = afp_root, dirs = dirs, select_dirs = select_dirs, infos = infos, numa_shuffling =
        numa_shuffling, max_jobs = max_jobs, fresh_build = fresh_build, export_files = export_files,
        augment_options = augment_options, session_setup = session_setup, cache = cache)

    val session_results =
      if (build_result.ok) {
        val trusted =
          (for {
            session <-
              sessions_structure.imports_selection(Sessions.Selection(sessions = trusted_sessions))
            (_, thy) <- build_result.deps(session).known_theories
          } yield thy.name).toSet

        for {
          session <- sessions_structure.build_selection(selection)
          if !is_trusted(session)
        } yield session -> {
          val base = build_result.deps(session)

          val theories =
            for {
              (_, thy) <- base.known_theories.toList
              node_name = thy.name
              if !trusted(node_name)
            } yield node_name

          check_session(options, build_result.deps.background(session), theories, trusted =
            trusted.toList, cache = cache, progress = progress)
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

        val total_timing =
          results.sessions.keys.map(a => results.build(a).timing).foldLeft(Timing.zero)(_ + _).
            copy(elapsed = elapsed_time)
        progress.echo(total_timing.message_resources)

        sys.exit(results.rc)
      })
}

class Check_Build_Tools extends Isabelle_Scala_Tools(Check_Build.isabelle_tool)

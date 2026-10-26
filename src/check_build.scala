/*  Title:      check_build.scala
    Author:     Fabian Huch

Command-line tools to build and check proofterms of Isabelle sessions.
*/

package isabelle

import scala.collection.mutable


object Check_Build {
  def check_build(
    options: Options,
    private_dir: Option[Path] = None,
    selection: Sessions.Selection = Sessions.Selection.empty,
    trusted_sessions: List[String] = Nil,
    browser_info: Browser_Info.Config = Browser_Info.Config.none,
    progress: Progress = new Progress,
    check_unknown_files: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    afp_root: Option[Path] = None,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    infos: List[Sessions.Info] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Option[Int] = None,
    list_files: Boolean = false,
    fresh_build: Boolean = false,
    no_build: Boolean = false,
    soft_build: Boolean = false,
    export_files: Boolean = false,
    augment_options: String => Options.Update = _ => Nil,
    session_setup: (String, Session) => Unit = (_, _) => (),
    cache: Rich_Text.Cache = Rich_Text.Cache.make()
  ): Build.Results = {
    ???
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
        var soft_build = false
        val exclude_session_groups = new mutable.ListBuffer[String]
        var all_sessions = false
        var build_heap = false
        var clean_build = false
        val dirs = new mutable.ListBuffer[Path]
        var export_files = false
        var fresh_build = false
        val session_groups = new mutable.ListBuffer[String]
        var max_jobs: Option[Int] = None
        var list_files = false
        var no_build = false
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
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -e           export files from session specification into file-system
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs
                 (default: 1 for local build, 0 for build cluster)
    -l           list session source files
    -n           no build -- take existing session build databases
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
          "S" -> (_ => soft_build = true),
          "X:" -> (arg => exclude_session_groups += arg),
          "a" -> (_ => all_sessions = true),
          "b" -> (_ => build_heap = true),
          "c" -> (_ => clean_build = true),
          "d:" -> (arg => dirs += Path.explode(arg)),
          "e" -> (_ => export_files = true),
          "f" -> (_ => fresh_build = true),
          "g:" -> (arg => session_groups += arg),
          "j:" -> (arg => max_jobs = Some(Value.Nat.parse(arg))),
          "l" -> (_ => list_files = true),
          "n" -> (_ => no_build = true),
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
            build_heap = build_heap,
            clean_build = clean_build,
            afp_root = afp_root,
            dirs = dirs.toList,
            select_dirs = select_dirs.toList,
            numa_shuffling = Host.numa_check(progress, numa_shuffling),
            max_jobs = max_jobs,
            list_files = list_files,
            fresh_build = fresh_build,
            no_build = no_build,
            soft_build = soft_build,
            export_files = export_files)

        val stop_date = progress.now()
        val elapsed_time = stop_date - progress.start

        progress.echo("\nFinished at " + Build_Log.print_date(stop_date), verbose = true)

        val total_timing =
          results.sessions.iterator.map(a => results(a).timing).foldLeft(Timing.zero)(_ + _).
            copy(elapsed = elapsed_time)
        progress.echo(total_timing.message_resources)

        sys.exit(results.rc)
      })
}

class Check_Build_Tools extends Isabelle_Scala_Tools(Check_Build.isabelle_tool)

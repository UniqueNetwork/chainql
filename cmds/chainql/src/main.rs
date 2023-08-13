use std::{io::Read, process};

use chainql_core::create_cql;
use clap::Parser;
use jrsonnet_cli::{InputOpts, MiscOpts, StdOpts, TlaOpts, TraceOpts};
use jrsonnet_evaluator::{apply_tla, bail, error::Result, manifest::JsonFormat, State, Thunk, Val};
use tokio::runtime::Handle;

/// chainql
#[derive(Parser)]
struct Opts {
	#[clap(flatten)]
	input: InputOpts,
	#[clap(flatten)]
	std: StdOpts,
	#[clap(flatten)]
	tla: TlaOpts,
	#[clap(flatten)]
	trace: TraceOpts,
	#[clap(flatten)]
	misc: MiscOpts,
	#[clap(long, short = 'S')]
	string: bool,
}
/// Set up Jrsonnet.
fn main_jrsonnet(s: State, opts: Opts) -> Result<String> {
	let import_resolver = opts.misc.import_resolver();
	s.set_import_resolver(import_resolver);
	if let Some(std) = opts.std.context_initializer(&s)? {
		s.set_context_initializer(std);
	}
	s.add_global("cql".into(), Thunk::evaluated(Val::Obj(create_cql())));

	// Resolve the Jsonnet code supplied to chainql.
	let res = if opts.input.exec {
		s.evaluate_snippet("<exec>".to_owned(), opts.input.input)?
	} else if opts.input.input == "-" {
		let mut buf = String::new();
		std::io::stdin()
			.read_to_string(&mut buf)
			.expect("read stdin");
		s.evaluate_snippet("<exec>".to_owned(), buf)?
	} else {
		let mut path = std::env::current_dir().expect("cwd");
		path.push(opts.input.input);
		s.import(path)?
	};
	let tla = opts.tla.tla_opts()?;
	// Supply the Jsonnet code with top level arguments.
	let res = apply_tla(s, &tla, res)?;

	// Output the result as either string or JSON.
	Ok(if opts.string {
		let res = if let Some(str) = res.as_str() {
			str.as_str().to_owned()
		} else {
			bail!("expected string as output")
		};
		res
	} else {
		let res = res.manifest(JsonFormat::cli(3, true))?;
		res.as_str().to_owned()
	})
}

fn main_sync() {
	let s = State::default();
	let opts = Opts::parse();
	let trace_format = opts.trace.trace_format();
	match main_jrsonnet(s, opts) {
		Ok(e) => {
			println!("{e}");
			process::exit(0)
		}
		Err(e) => {
			eprintln!("{}", trace_format.format(&e).unwrap());
			process::exit(1)
		}
	}
}

#[tokio::main]
async fn main() {
	Handle::current()
		.spawn_blocking(main_sync)
		.await
		.expect("jrsonnet should not panic");
}

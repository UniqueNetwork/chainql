use std::{io::Read, process};

use clap::Parser;
use jrsonnet_cli::{InputOpts, MiscOpts, StdOpts, TlaOpts, TraceOpts};
use jrsonnet_evaluator::{apply_tla, bail, error::Result, manifest::JsonFormat, State};
use tokio::runtime::Handle;
use tracing_indicatif::IndicatifLayer;
use tracing_subscriber::{
	fmt::writer::MakeWriterExt, layer::SubscriberExt, util::SubscriberInitExt,
};

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
fn main_jrsonnet(opts: Opts) -> Result<String> {
	let indicatif_layer = IndicatifLayer::new();
	tracing_subscriber::registry()
		.with(
			tracing_subscriber::fmt::layer().without_time().with_writer(
				indicatif_layer
					.get_stderr_writer()
					.with_max_level(tracing::Level::INFO),
			),
		)
		.with(indicatif_layer)
		.init();

	let import_resolver = opts.misc.import_resolver();

	let mut sb = State::builder();
	sb.import_resolver(import_resolver);
	if let Some(std) = opts.std.context_initializer()? {
		sb.context_initializer((chainql_core::CqlContextInitializer::default(), std));
	} else {
		sb.context_initializer(chainql_core::CqlContextInitializer::default());
	}

	let s = sb.build();

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
	let opts = Opts::parse();
	let trace_format = opts.trace.trace_format();
	match main_jrsonnet(opts) {
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

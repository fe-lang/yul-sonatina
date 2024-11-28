use std::{fs, path::PathBuf};

use clap::Parser;
use sonatina_ir::ir_writer::ModuleWriter;
use yul_sonatina::compile;

fn main() {
    let args = Args::parse();
    let input = args.input_file;
    let output = args.output.unwrap_or_else(|| {
        let stem = input.file_stem().unwrap().to_str().unwrap();
        let mut output = std::env::current_dir().unwrap();
        output.push(format!("{stem}.sntn"));
        output
    });

    let src = match fs::read_to_string(input) {
        Ok(src) => src,
        Err(err) => {
            eprintln!("{err}");
            std::process::exit(err.raw_os_error().unwrap());
        }
    };

    let module = match compile(&src) {
        Ok(module) => module,
        Err(err) => {
            eprintln!("{err}");
            std::process::exit(1);
        }
    };

    let ir_text = ModuleWriter::new(&module).dump_string();
    if let Err(err) = fs::write(output, ir_text.as_bytes()) {
        eprintln!("{err}");
        std::process::exit(err.raw_os_error().unwrap());
    }
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// The Yul source file to process
    input_file: PathBuf,

    /// The output Sonatina file name (optional)t file to process
    #[arg(short, long)]
    output: Option<PathBuf>,
}

use clap::Parser;
use lifelib::PatternParser;

#[derive(Clone, Debug, Eq, Parser, PartialEq)]
struct Arguments {
    #[arg(short, long, default_value_t = 1)]
    number: usize,

    #[arg(default_value_t)]
    infile: patharg::InputArg,
}

fn main() -> std::io::Result<()> {
    let args = Arguments::parse();
    let source = args.infile.read_to_string()?;
    let mut pattern = PatternParser::dead_chars(" .").parse(&source);
    for _ in 0..args.number {
        pattern = pattern.step();
    }
    println!("{}", pattern.draw('.', '#'));
    Ok(())
}

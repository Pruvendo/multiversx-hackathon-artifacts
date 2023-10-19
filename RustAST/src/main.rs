fn main() {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let fname = match &args[..] {
        [fname] => fname,
        _ => panic!()
    };
    let content = std::fs::read_to_string(fname).unwrap();
    let ast = syn::parse_file(&content).unwrap();
    let s = syn_serde::json::to_string_pretty(&ast);
    println!("{}", s);
}

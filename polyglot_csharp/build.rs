use std::process::Command;

fn main() {
    let udl_file = "./src/polyglot_csharp.udl";
    let out_dir = "./bindings/";
    let r = uniffi::generate_scaffolding(udl_file);
    println!("{:?}", r);
    Command::new("uniffi-bindgen-cs")
        .arg("--out-dir")
        .arg(out_dir)
        .arg(udl_file)
        .args(["--config", "unify.toml"])
        .output()
        .expect("Failed when generating C# bindings");
}

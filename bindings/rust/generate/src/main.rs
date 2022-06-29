use std::path::{Path, PathBuf};
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufRead, BufReader};
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
#[derive(Debug)]
struct SymbolCallback {
    prefix: String,
}

impl SymbolCallback {
    fn new() -> Self {
        SymbolCallback {
            prefix: format!("{}_", prefix_string()),
        }
    }
}

impl bindgen::callbacks::ParseCallbacks for SymbolCallback {
    fn generated_name_override(&self, function_name: &str) -> Option<String> {
        let mut result = function_name.to_string();
        if result.starts_with(&self.prefix) {
            result = result.replace(&self.prefix, "");
            Some(result)
        } else {
            None
        }
    }
}
*/



fn main() {
    let out_dir = std::env::args().nth(1).expect("missing sys dir");
    let out_dir = Path::new(&out_dir);

    let symbol_file = std::env::args().nth(2).expect("missing symbol file");
    let symbol_file = Path::new(&symbol_file);

    let symbol_set = collect_symbols(symbol_file);

    let bindings_file = out_dir.join("src").join("bindings.rs");

    let builder = prepare_bindings_builder(out_dir, None);
    let bindings = builder.generate().expect("Unable to generate bindings.");
    bindings.write_to_file(bindings_file).expect("Unable to write bindings to file.");

    println!("There are {} symbols.", symbol_set.len());
}

fn collect_symbols(symbol_file: &Path) -> HashSet<String> {
    let mut symbol_set = HashSet::new();
    let symbol_file = File::open(symbol_file).unwrap();
    let reader = BufReader::new(symbol_file);
    for line in reader.lines() {
        symbol_set.insert(line.unwrap());
    }

    symbol_set
}

fn find_include_path(out_dir: &Path) -> PathBuf {
    out_dir
        .join("deps")
        .join("aws-lc")
        .join("include")
}

fn prepare_clang_args(out_dir: &Path, build_prefix: Option<&str>) -> Vec<String> {
    let mut clang_args: Vec<String> = Vec::new();

    clang_args.push("-I".to_string());
    clang_args.push(find_include_path(out_dir).display().to_string());
    if let Some(prefix) = build_prefix {
        clang_args.push(format!("-DBORINGSSL_PREFIX={}", prefix));
    }

    clang_args
}

const COPYRIGHT: &str = r#"
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
"#;

const PRELUDE: &str = r#"
#![allow(unused_imports, non_camel_case_types, non_snake_case, non_upper_case_globals, improper_ctypes)]
"#;

fn prepare_bindings_builder(out_dir: &Path, build_prefix: Option<&str>) -> bindgen::Builder {

    let clang_args = prepare_clang_args(out_dir, build_prefix);

    let builder = bindgen::Builder::default()
        .derive_copy(true)
        .derive_debug(true)
        .derive_default(true)
        .derive_eq(true)
        .default_enum_style(bindgen::EnumVariation::NewType { is_bitfield: false })
        .default_macro_constant_type(bindgen::MacroTypeVariation::Signed)
        .generate_comments(true)
        .fit_macro_constants(false)
        .size_t_is_usize(true)
        .layout_tests(true)
        .prepend_enum_name(true)
        .rustfmt_bindings(true)
        .clang_args(clang_args)
        .raw_line(COPYRIGHT)
        .raw_line(PRELUDE)
        .header(find_include_path(out_dir).join("rust_wrapper.h").display().to_string());

    builder
}
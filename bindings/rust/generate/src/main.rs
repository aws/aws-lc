use std::path::{Path, PathBuf};
use std::collections::HashSet;
use std::{fs, io};
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use regex::Regex;

/*
// See PR: https://github.com/rust-lang/rust-bindgen/pull/2228

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

fn modify_bindings(bindings_path: &PathBuf, prefix: &str) -> io::Result<()>{
    // Needed until this issue is resolved: https://github.com/rust-lang/rust-bindgen/issues/1375

    let prefix_func_detector = Regex::new(&format!("(^\\s+)pub\\s+fn\\s+{}_(\\w*)(.*)", prefix)).unwrap();
    let output_path = bindings_path.parent().unwrap().join("updated_bindings.rs");
    let bindings_reader = BufReader::new(File::open(&bindings_path)?);
    let mut bindings_writer = BufWriter::new(File::create(&output_path)?);
    for line in bindings_reader.lines() {
        let line = line.unwrap().clone();
        if let Some(captures) = prefix_func_detector.captures(&line) {
            let line_start = &captures[1];
            let name_position = line_start.len();
            let fn_name = &captures[2];
            let line_end = &captures[3];
            let link_line_start = (0..name_position).map(|_| " ").collect::<String>();
            bindings_writer.write_fmt(format_args!("{}#[link_name=\"{}_{}\"]\n", link_line_start, prefix, fn_name))?;
            bindings_writer.write_fmt(format_args!("{}pub fn {}{}\n", line_start, fn_name, line_end))?;
        } else {
            bindings_writer.write_fmt(format_args!("{}\n", &line))?;
        }
    }
    bindings_writer.flush()?;
    fs::remove_file(bindings_path)?;
    fs::rename(output_path, bindings_path)?;
    Ok(())
}

fn find_include_path(out_dir: &Path) -> PathBuf {
    out_dir
        .join("deps")
        .join("aws-lc")
        .join("include")
}

fn compute_prefix(version: &str) -> String {
    format!("aws_lc_{}", version.to_string().replace('.', "_"))
}

fn prepare_clang_args(out_dir: &Path, build_prefix: Option<&str>) -> Vec<String> {
    let mut clang_args: Vec<String> = vec![
        "-I".to_string(),
        find_include_path(out_dir).display().to_string()
    ];

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

fn main() -> io::Result<()> {
    let out_dir = std::env::args().nth(1).expect("missing sys dir");
    let out_dir = Path::new(&out_dir);

    let aws_lc_sys_version = std::env::args().nth(2).expect("missing aws-lc-sys version");
    let prefix = compute_prefix(&aws_lc_sys_version);

    let bindings_file = out_dir.join("src").join("bindings.rs");

    let builder = prepare_bindings_builder(out_dir, Some(&prefix));
    let bindings = builder.generate().expect("Unable to generate bindings.");
    bindings.write_to_file(&bindings_file).expect("Unable to write bindings to file.");
    modify_bindings(&bindings_file, &prefix)?;

    Ok(())
}
/* Copyright (c) 2022, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

// SPDX-License-Identifier: Apache-2.0 OR ISC
// Modifications Copyright Amazon.com, Inc. or its affiliates. See GitHub history for details.

use bindgen::callbacks::ParseCallbacks;
use std::fmt::Debug;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

#[derive(Debug)]
struct StripPrefixCallback {
    remove_prefix: Option<String>,
}

impl StripPrefixCallback {
    fn new(prefix: &str) -> StripPrefixCallback {
        StripPrefixCallback {
            remove_prefix: Some(prefix.to_string()),
        }
    }
}

impl ParseCallbacks for StripPrefixCallback {
    fn generated_name_override(&self, name: &str) -> Option<String> {
        self.remove_prefix.as_ref().map_or(None, |s| {
            let prefix = format!("{}_", s);
            name.strip_prefix(prefix.as_str())
                .map_or(None, |s| Some(String::from(s)))
        })
    }
}

fn get_include_path(manifest_dir: &Path) -> PathBuf {
    manifest_dir.join("deps").join("aws-lc").join("include")
}

fn prepare_clang_args(manifest_dir: &Path, build_prefix: Option<&str>) -> Vec<String> {
    let mut clang_args: Vec<String> = vec![
        "-I".to_string(),
        get_include_path(manifest_dir).display().to_string(),
    ];

    if let Some(prefix) = build_prefix {
        clang_args.push(format!("-DBORINGSSL_PREFIX={}", prefix));
    }

    clang_args
}

const COPYRIGHT: &str = r#"
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
"#;

const PRELUDE: &str = r#"
#![allow(unused_imports, non_camel_case_types, non_snake_case, non_upper_case_globals, improper_ctypes)]
"#;

fn prepare_bindings_builder(manifest_dir: &Path, build_prefix: Option<&str>) -> bindgen::Builder {
    let clang_args = prepare_clang_args(manifest_dir, build_prefix);

    let mut builder = bindgen::Builder::default()
        .derive_copy(true)
        .derive_debug(true)
        .derive_default(true)
        .derive_eq(true)
        .allowlist_file(".*/openssl/[^/]+\\.h")
        .allowlist_file(".*/rust_wrapper\\.h")
        .default_enum_style(bindgen::EnumVariation::NewType {
            is_bitfield: false,
            is_global: false,
        })
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
        .header(
            get_include_path(manifest_dir)
                .join("rust_wrapper.h")
                .display()
                .to_string(),
        );

    if let Some(ps) = build_prefix {
        builder = builder.parse_callbacks(Box::new(StripPrefixCallback::new(ps)));
    }

    builder
}

const AWS_LC_PATH: &str = "deps/aws-lc";

#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum OutputLib {
    Crypto,
    Ssl,
}

#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum OutputLibType {
    Static,
    Dynamic,
}

impl OutputLibType {
    fn rust_lib_type(&self) -> &str {
        match self {
            OutputLibType::Static => "static",
            OutputLibType::Dynamic => "dylib",
        }
    }
    fn lib_extension(&self) -> &str {
        match self {
            OutputLibType::Static => "a",
            OutputLibType::Dynamic => "so",
        }
    }
}

impl OutputLib {
    fn filename(&self, libtype: OutputLibType, prefix: Option<&str>) -> String {
        format!("lib{}.{}", &self.libname(prefix), libtype.lib_extension())
    }

    fn libname(&self, prefix: Option<&str>) -> String {
        format!(
            "{}{}",
            if let Some(pfix) = prefix.to_owned() {
                pfix
            } else {
                ""
            },
            match self {
                OutputLib::Crypto => "crypto",
                OutputLib::Ssl => "ssl",
            }
        )
    }

    fn locate_dir(&self, path: &Path) -> PathBuf {
        path.join(Path::new(&format!("build/{}", self.libname(None))))
            .join(get_platform_output_path())
    }

    fn locate_file(&self, path: &Path, libtype: OutputLibType, prefix: Option<&str>) -> PathBuf {
        self.locate_dir(path).join(self.filename(libtype, prefix))
    }
}

fn get_platform_output_path() -> PathBuf {
    PathBuf::new()
}

fn get_cmake_config() -> cmake::Config {
    let pwd = env::current_dir().unwrap();

    cmake::Config::new(pwd.join(AWS_LC_PATH))
}

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn prefix_string() -> String {
    format!("aws_lc_{}", VERSION.to_string().replace('.', "_"))
}

fn test_cmake_command(executable: &str) -> bool {
    if let Ok(output) = Command::new(executable).arg("--version").output() {
        return output.status.success();
    }
    false
}

fn prepare_cmake_build(build_prefix: Option<&str>) -> cmake::Config {
    if test_cmake_command("cmake3") {
        env::set_var("CMAKE", "cmake3");
    } else {
        env::set_var("CMAKE", "cmake");
    }

    let mut cmake_cfg = get_cmake_config();

    let opt_level = env::var("OPT_LEVEL").unwrap_or_else(|_| "0".to_string());
    if opt_level.ne("0") {
        if opt_level.eq("1") || opt_level.eq("2") {
            cmake_cfg.define("CMAKE_BUILD_TYPE", "relwithdebinfo");
        } else {
            cmake_cfg.define("CMAKE_BUILD_TYPE", "release");
        }
    }

    if let Some(symbol_prefix) = build_prefix {
        cmake_cfg.define("BORINGSSL_PREFIX", symbol_prefix);
        let pwd = env::current_dir().unwrap();
        let include_path = pwd.join(AWS_LC_PATH).join("include");
        cmake_cfg.define(
            "BORINGSSL_PREFIX_HEADERS",
            include_path.display().to_string(),
        );
    }

    if cfg!(feature = "asan") {
        env::set_var("CC", "/usr/bin/clang");
        env::set_var("CXX", "/usr/bin/clang++");
        env::set_var("ASM", "/usr/bin/clang");

        cmake_cfg.define("ASAN", "1");
    }

    cmake_cfg
}

fn build_aws_lc() -> PathBuf {
    let mut cmake_cfg = prepare_cmake_build(Some(&prefix_string()));

    cmake_cfg.build_target("crypto").build()
}

fn main() -> Result<(), String> {
    use crate::OutputLib::Crypto;
    use crate::OutputLibType::Static;

    let manifest_dir = env::current_dir().unwrap();
    let manifest_dir = dunce::canonicalize(&Path::new(&manifest_dir)).unwrap();
    let prefix = prefix_string();

    let bindings_file = manifest_dir.join("src").join("bindings.rs");

    let builder = prepare_bindings_builder(&manifest_dir, Some(&prefix));
    let bindings = builder.generate().expect("Unable to generate bindings.");
    bindings
        .write_to_file(&bindings_file)
        .expect("Unable to write bindings to file.");

    let aws_lc_dir = build_aws_lc();

    let lib_file = Crypto.locate_file(&aws_lc_dir, Static, None);
    let prefixed_lib_file = Crypto.locate_file(&aws_lc_dir, Static, Some(&prefix));
    fs::rename(lib_file, prefixed_lib_file).expect("Unexpected error: Library not found");

    let libcrypto_dir = Crypto.locate_dir(&aws_lc_dir);
    println!("cargo:rustc-link-search=native={}", libcrypto_dir.display());

    println!(
        "cargo:rustc-link-lib={}={}",
        Static.rust_lib_type(),
        Crypto.libname(Some(&prefix))
    );
    println!(
        "cargo:include={}",
        get_include_path(&manifest_dir).display()
    );
    println!("cargo:rerun-if-changed=build.rs");

    Ok(())
}

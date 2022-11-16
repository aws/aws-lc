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
use std::ffi::{OsStr, OsString};
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
        self.remove_prefix.as_ref().and_then(|s| {
            let prefix = format!("{}_", s);
            name.strip_prefix(prefix.as_str()).map(String::from)
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

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn prefix_string() -> String {
    format!("aws_lc_{}", VERSION.to_string().replace('.', "_"))
}

fn test_command(executable: &OsStr, args: &[&OsStr]) -> bool {
    if let Ok(output) = Command::new(executable).args(args).output() {
        return output.status.success();
    }
    false
}

fn find_cmake_command() -> Option<&'static OsStr> {
    if test_command("cmake3".as_ref(), &["--version".as_ref()]) {
        Some("cmake3".as_ref())
    } else if test_command("cmake".as_ref(), &["--version".as_ref()]) {
        Some("cmake".as_ref())
    } else {
        None
    }
}

fn prepare_cmake_args(
    aws_lc_path: &Path,
    build_prefix: Option<&str>,
) -> Result<Vec<OsString>, &'static str> {
    let mut args: Vec<OsString> = vec![
        OsString::from("-DBUILD_TESTING=OFF"),
        OsString::from("-DBUILD_LIBSSL=OFF"),
        OsString::from("-DDISABLE_PERL=ON"),
        OsString::from("-DDISABLE_GO=ON"),
        aws_lc_path.as_os_str().into(),
    ];

    let opt_level = env::var("OPT_LEVEL").unwrap_or_else(|_| "0".to_string());
    if opt_level.eq("0") {
        args.push(OsString::from("-DCMAKE_BUILD_TYPE=debug"));
    } else if opt_level.eq("1") || opt_level.eq("2") {
        args.push(OsString::from("-DCMAKE_BUILD_TYPE=relwithdebinfo"));
    } else {
        args.push(OsString::from("-DCMAKE_BUILD_TYPE=release"));
    }

    if let Some(symbol_prefix) = build_prefix {
        args.push(OsString::from(format!(
            "-DBORINGSSL_PREFIX={}",
            symbol_prefix
        )));
        let include_path = aws_lc_path.join("include");
        args.push(OsString::from(format!(
            "-DBORINGSSL_PREFIX_HEADERS={}",
            include_path.display()
        )));
    }

    if cfg!(feature = "asan") {
        env::set_var("CC", "/usr/bin/clang");
        env::set_var("CXX", "/usr/bin/clang++");
        env::set_var("ASM", "/usr/bin/clang");

        args.push(OsString::from("-DASAN=1"));
    }

    Ok(args)
}

fn load_env_var(var_name: &str) -> String {
    env::var(var_name).unwrap_or_else(|_| panic!("Missing Environment variable: {}", var_name))
}

fn build_aws_lc() -> Result<PathBuf, &'static str> {
    let Some(cmake_cmd) = find_cmake_command() else {
        return Err("Missing dependency: cmake");
    };

    let pwd = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let aws_lc_path = pwd.join(AWS_LC_PATH);

    let out_dir = PathBuf::from(load_env_var("OUT_DIR"));
    let build_dir = out_dir.join("build");
    if !build_dir.exists() {
        fs::create_dir_all(build_dir.clone()).unwrap();
    }

    let mut setup_command = Command::new(cmake_cmd);

    setup_command.args(prepare_cmake_args(&aws_lc_path, Some(&prefix_string()))?);
    setup_command.current_dir(&build_dir);
    println!("running: {:?}", setup_command);
    let output = setup_command
        .output()
        .map_err(|_| "cmake setup command failed")?;

    if !output.status.success() {
        eprintln!("{}", String::from_utf8(output.stderr).unwrap());
        return Err("cmake setup command unsuccessful");
    }

    let mut build_command = Command::new(cmake_cmd);
    build_command.args(&[
        OsString::from("--build"),
        OsString::from("."),
        OsString::from("--target"),
        OsString::from("crypto"),
    ]);
    build_command.current_dir(&build_dir);

    println!("running: {:?}", build_command);
    let output = build_command
        .output()
        .map_err(|_| "cmake build command failed")?;
    if !output.status.success() {
        eprintln!("-- stdout --");
        eprintln!("{}", String::from_utf8(output.stdout).unwrap());
        eprintln!("-- stderr --");
        eprintln!("{}", String::from_utf8(output.stderr).unwrap());
        return Err("cmake build command unsuccessful.");
    }

    Ok(out_dir)
}

fn main() -> Result<(), String> {
    use crate::OutputLib::Crypto;
    use crate::OutputLibType::Static;

    let mut missing_dependency = false;

    if let Some(cmake_cmd) = find_cmake_command() {
        env::set_var("CMAKE", cmake_cmd);
    } else {
        eprintln!("Missing dependency: cmake");
        missing_dependency = true;
    };

    if missing_dependency {
        panic!("Required build dependency is missing. Halting build.");
    }

    let manifest_dir = env::current_dir().unwrap();
    let manifest_dir = dunce::canonicalize(Path::new(&manifest_dir)).unwrap();
    let prefix = prefix_string();

    let bindings_file = manifest_dir.join("src").join("bindings.rs");

    let builder = prepare_bindings_builder(&manifest_dir, Some(&prefix));
    let bindings = builder.generate().expect("Unable to generate bindings.");
    bindings
        .write_to_file(bindings_file)
        .expect("Unable to write bindings to file.");

    let aws_lc_dir = build_aws_lc()?;

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

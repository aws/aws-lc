// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

const AWS_LC_PATH: &str = "deps/aws-lc";

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
}

impl OutputLib {
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

fn verify_fips_clang_version() -> (&'static str, &'static str) {
    fn version(tool: &str) -> String {
        let output = match Command::new(tool).arg("--version").output() {
            Ok(o) => o,
            Err(e) => {
                eprintln!("warning: missing {}, trying other compilers: {}", tool, e);
                // NOTE: hard-codes that the loop below checks the version
                return String::new();
            }
        };
        assert!(output.status.success());
        let output = std::str::from_utf8(&output.stdout).expect("invalid utf8 output");
        output.lines().next().expect("empty output").to_string()
    }

    const REQUIRED_CLANG_VERSION: &str = "7.0.1";
    for (cc, cxx) in [
        ("clang-7", "clang++-7"),
        ("clang", "clang++"),
        ("cc", "c++"),
    ] {
        let cc_version = version(cc);
        if cc_version.contains(REQUIRED_CLANG_VERSION) {
            assert!(
                version(cxx).contains(REQUIRED_CLANG_VERSION),
                "mismatched versions of cc and c++"
            );
            return (cc, cxx);
        } else if cc == "cc" {
            panic!(
                "unsupported clang version \"{}\": FIPS requires clang {}",
                cc_version, REQUIRED_CLANG_VERSION
            );
        } else if !cc_version.is_empty() {
            eprintln!(
                "warning: FIPS requires clang version {}, skipping incompatible version \"{}\"",
                REQUIRED_CLANG_VERSION, cc_version
            );
        }
    }
    unreachable!()
}

fn test_cmake_command(executable: &str) -> bool {
    if let Ok(output) = Command::new(executable).arg("--version").output() {
        return output.status.success();
    }
    false
}

fn prepare_cmake_build(
    build_fips: bool,
    build_prefix: Option<&str>) -> cmake::Config {

    if test_cmake_command("cmake3") {
        env::set_var("CMAKE", "cmake3");
    } else {
        env::set_var("CMAKE", "cmake");
    }

    let mut cmake_cfg = get_cmake_config();

    if build_fips {
        let (clang, clangxx) = verify_fips_clang_version();
        cmake_cfg.define("CMAKE_C_COMPILER", clang);
        cmake_cfg.define("CMAKE_CXX_COMPILER", clangxx);
        cmake_cfg.define("CMAKE_ASM_COMPILER", clang);
        cmake_cfg.define("FIPS", "1");
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

    cmake_cfg
}

fn build_aws_lc() -> Result<PathBuf, String> {
    let mut cmake_cfg = prepare_cmake_build(false, Some(&prefix_string()));
    let output_dir = cmake_cfg.build_target("ssl").build();

    Ok(output_dir)
}

fn main() -> Result<(), String> {
    use crate::OutputLib::{Crypto, Ssl};
    use crate::OutputLibType::Static;

    let aws_lc_dir = build_aws_lc()?;

    let libcrypto_dir = Crypto.locate_dir(&aws_lc_dir);
    let libssl_dir = Ssl.locate_dir(&aws_lc_dir);
    println!("cargo:rustc-link-search=native={}", libcrypto_dir.display());
    println!("cargo:rustc-link-search=native={}", libssl_dir.display());
    println!(
        "cargo:rustc-link-lib={}={}",
        Static.rust_lib_type(),
        Crypto.libname(None)
    );
    println!(
        "cargo:rustc-link-lib={}={}",
        Static.rust_lib_type(),
        Ssl.libname(None)
    );

    Ok(())
}
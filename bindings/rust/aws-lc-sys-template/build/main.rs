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

use cfg_aliases::cfg_aliases;
#[cfg(feature = "bindgen")]
use std::default::Default;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

#[cfg(feature = "bindgen")]
mod bindgen;

pub(crate) fn get_include_path(manifest_dir: &Path) -> PathBuf {
    manifest_dir.join("deps").join("aws-lc").join("include")
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

#[cfg(feature = "internal_generate")]
fn target_platform_prefix(name: &str) -> String {
    format!(
        "{}_{}_{}",
        std::env::consts::OS,
        std::env::consts::ARCH,
        name
    )
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

fn get_cmake_config() -> cmake::Config {
    let pwd = env::current_dir().unwrap();

    cmake::Config::new(pwd.join(AWS_LC_PATH))
}

fn prepare_cmake_build(build_prefix: Option<&str>) -> cmake::Config {
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

    // Build flags that minimize our crate size.
    cmake_cfg.define("BUILD_TESTING", "OFF");
    cmake_cfg.define("BUILD_LIBSSL", "ON");
    // Build flags that minimize our dependencies.
    cmake_cfg.define("DISABLE_PERL", "ON");
    cmake_cfg.define("DISABLE_GO", "ON");

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

    // cmake supports passing multiple arguments to target, but this is broken in the cmake crate
    // ssl requires crypto so we can get away with just picking the top-most requried one.
    let target = if cfg!(feature = "ssl") {
        Some("ssl")
    } else {
        Some("crypto")
    };

    cmake_cfg.build_target(target.unwrap()).build()
}

#[cfg(feature = "bindgen")]
fn generate_bindings(manifest_dir: &PathBuf, prefix: &str, bindings_path: &PathBuf) {
    let options = bindgen::BindingOptions {
        build_prefix: Some(&prefix),
        include_ssl: cfg!(feature = "ssl"),
        disable_prelude: true,
        ..Default::default()
    };

    let bindings =
        bindgen::generate_bindings(&manifest_dir, options).expect("Unable to generate bindings.");

    bindings
        .write(Box::new(std::fs::File::create(&bindings_path).unwrap()))
        .expect("written bindings");
}

#[cfg(feature = "internal_generate")]
fn generate_src_bindings(manifest_dir: &PathBuf, prefix: &str, src_bindings_path: &PathBuf) {
    bindgen::generate_bindings(
        &manifest_dir,
        bindgen::BindingOptions {
            build_prefix: Some(&prefix),
            include_ssl: false,
            ..Default::default()
        },
    )
    .expect("Unable to generate bindings.")
    .write_to_file(src_bindings_path.join(format!("{}.rs", target_platform_prefix("crypto"))))
    .expect("write bindings");

    bindgen::generate_bindings(
        &manifest_dir,
        bindgen::BindingOptions {
            build_prefix: Some(&prefix),
            include_ssl: true,
            ..Default::default()
        },
    )
    .expect("Unable to generate bindings.")
    .write_to_file(src_bindings_path.join(format!("{}.rs", target_platform_prefix("crypto_ssl"))))
    .expect("write bindings");
}

fn main() -> Result<(), String> {
    use crate::OutputLib::{Crypto, Ssl};
    use crate::OutputLibType::Static;

    cfg_aliases! {
        linux_x86: { all(not(feature = "bindgen"), target_os = "linux", target_arch = "x86") },
        linux_x86_64: { all(not(feature = "bindgen"), target_os = "linux", target_arch = "x86_64") },
        linux_aarch64: { all(not(feature = "bindgen"), target_os = "linux", target_arch = "aarch64") },
        macos_x86_64: { all(not(feature = "bindgen"), target_os = "macos", target_arch = "x86_64") },
        not_pregenerated: { not(any(linux_x86, linux_aarch64, linux_x86_64, macos_x86_64)) },
    }

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

    #[cfg(feature = "internal_generate")]
    {
        let src_bindings_path = Path::new(&manifest_dir).join("src");
        generate_src_bindings(&manifest_dir, &prefix, &src_bindings_path);
    }

    #[cfg(feature = "bindgen")]
    {
        let gen_bindings_path = Path::new(&env::var("OUT_DIR").unwrap()).join("bindings.rs");
        generate_bindings(&manifest_dir, &prefix, &gen_bindings_path);
    }

    let aws_lc_dir = build_aws_lc();

    let libcrypto_file = Crypto.locate_file(&aws_lc_dir, Static, None);
    let prefixed_libcrypto_file = Crypto.locate_file(&aws_lc_dir, Static, Some(&prefix));
    fs::rename(libcrypto_file, prefixed_libcrypto_file)
        .expect("Unexpected error: Library not found");

    println!(
        "cargo:rustc-link-search=native={}",
        Crypto.locate_dir(&aws_lc_dir).display()
    );

    println!(
        "cargo:rustc-link-lib={}={}",
        Static.rust_lib_type(),
        Crypto.libname(Some(&prefix))
    );

    if cfg!(feature = "ssl") {
        let libssl_file = Ssl.locate_file(&aws_lc_dir, Static, None);
        let prefixed_libssl_file = Ssl.locate_file(&aws_lc_dir, Static, Some(&prefix));
        fs::rename(libssl_file, prefixed_libssl_file).expect("Unexpected error: Library not found");

        println!(
            "cargo:rustc-link-search=native={}",
            Ssl.locate_dir(&aws_lc_dir).display()
        );

        println!(
            "cargo:rustc-link-lib={}={}",
            Static.rust_lib_type(),
            Ssl.libname(Some(&prefix))
        );
    }

    println!(
        "cargo:include={}",
        get_include_path(&manifest_dir).display()
    );

    println!("cargo:rerun-if-changed=build/");
    Ok(())
}

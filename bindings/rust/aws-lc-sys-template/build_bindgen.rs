// SPDX-License-Identifier: Apache-2.0 OR ISC
// Modifications Copyright Amazon.com, Inc. or its affiliates. See GitHub history for details.

use crate::get_include_path;
use bindgen::callbacks::ParseCallbacks;
use std::fmt::Debug;
use std::path::Path;

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

#[cfg(feature = "bindgen")]
impl ParseCallbacks for StripPrefixCallback {
    fn generated_name_override(&self, name: &str) -> Option<String> {
        self.remove_prefix.as_ref().and_then(|s| {
            let prefix = format!("{}_", s);
            name.strip_prefix(prefix.as_str()).map(String::from)
        })
    }
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

#[cfg(feature = "internal_generate")]
pub(crate) fn target_platform_bindings_string() -> String {
    format!(
        "{}_{}_bindings.rs",
        std::env::consts::OS,
        std::env::consts::ARCH
    )
}

pub(crate) fn generate_bindings(
    manifest_dir: &Path,
    build_prefix: Option<&str>,
) -> Result<(), &'static str> {
    #[cfg(any(feature = "generate_bindings", not_pregenerated))]
    let bindings_file = manifest_dir.join("src").join("bindings.rs");
    #[cfg(feature = "internal_generate")]
    let bindings_file = manifest_dir
        .join("src")
        .join(target_platform_bindings_string());

    let builder = prepare_bindings_builder(&manifest_dir, build_prefix);
    let bindings = builder.generate().expect("Unable to generate bindings.");
    Ok(bindings
        .write_to_file(bindings_file)
        .expect("Unable to write bindings to file."))
}

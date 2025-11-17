#!/usr/bin/env python3

import argparse
import sys
import pathlib
import tomllib
import tempfile
import subprocess
import typing
import shutil
import filecmp

from vectorslib import utils, convert_vector, generate_spec
from vectorslib.utils import SyncError


def fetch_sources(
    clone_dir: pathlib.Path,
    sources: dict,
    using_custom_clone_dir: bool = False,
):
    for source_name, source_info in sources.items():
        source_clone_dir = clone_dir / source_name

        if source_clone_dir.is_dir():
            assert using_custom_clone_dir
            utils.warning(
                f"using existing, potentially stale upstream clone of {source_name} at {source_clone_dir}"
            )
        else:
            ret = subprocess.run(
                [
                    "git",
                    "clone",
                    "--branch",
                    source_info["branch"],
                    "--depth",
                    "1",
                    source_info["git_url"],
                    str(source_clone_dir),
                ],
                capture_output=True,
            )
            if ret.returncode != 0:
                raise SyncError(
                    f"failed to clone {source_name}: {ret.stderr.decode().strip()}"
                )

        assert source_clone_dir.is_dir()
        source_info["local_path"] = source_clone_dir


def update_sources(
    cwd: pathlib.Path,
    sources: dict,
    new_file: typing.Optional[str],
):
    # Ensure upstream directories exist
    for source_name, source_info in sources.items():
        source_info["upstream_path"].mkdir(parents=True, exist_ok=True)

    # Add new file first to catch invalid file names and sources early
    if new_file:
        file_path = pathlib.Path(new_file)
        source_name = file_path.parts[0]

        if source_name not in sources:
            raise SyncError(
                f"unknown source '{source_name}', expected one of: {list(sources.keys())}"
            )

        relative_path = pathlib.Path(*file_path.parts[1:])
        local_file = sources[source_name]["local_path"] / relative_path

        if not local_file.exists():
            raise SyncError(f"file not found in upstream repo: {relative_path}")
        if local_file.is_dir():
            raise SyncError(f"path is a directory, not a file: {relative_path}")

        upstream_file = sources[source_name]["upstream_path"] / relative_path
        if upstream_file.exists():
            raise SyncError(f"file already exists in upstream: {upstream_file}")

        upstream_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(local_file, upstream_file)
        utils.info(f"copied new file to upstream: {upstream_file}")

    # Update existing files from all sources
    missing_files = []
    for source_name, source_info in sources.items():
        upstream_path = source_info["upstream_path"]
        local_path = source_info["local_path"]

        for upstream_file in upstream_path.rglob("*"):
            if not upstream_file.is_file():
                continue

            relative_path = upstream_file.relative_to(upstream_path)
            local_file = local_path / relative_path

            if not local_file.exists():
                missing_files.append(f"{source_name}/{relative_path}")
            elif not filecmp.cmp(local_file, upstream_file, shallow=False):
                shutil.copy2(local_file, upstream_file)
                utils.info(f"updated upstream file: {source_name}/{relative_path}")

    if missing_files:
        files_list = "\n  ".join(missing_files)
        raise SyncError(
            f"the following files are in ./upstream but cannot be found in a new clone of the source repo:\n  {files_list}"
        )


def convert_sources(
    cwd: pathlib.Path,
    clone_dir: pathlib.Path,
    sources: dict,
):
    converted_dir = cwd / "converted"
    converted_dir.mkdir(parents=True, exist_ok=True)

    for source_name, source_info in sources.items():
        source_info["converted_path"] = converted_dir / source_name
        source_info["converted_path"].mkdir(parents=True, exist_ok=True)

    for source_name, source_info in sources.items():
        upstream_path = source_info["upstream_path"]
        converted_path = source_info["converted_path"]

        for upstream_file in upstream_path.rglob("*.json"):
            relative_path = upstream_file.relative_to(upstream_path)
            converted_file = converted_path / relative_path.with_suffix(".txt")

            converted_file.parent.mkdir(parents=True, exist_ok=True)

            try:
                convert_vector.convert_file(upstream_file, converted_file)
                utils.info(f"converted {source_name}/{relative_path}")
            except Exception as e:
                error_msg = f"failed to convert {source_name}/{relative_path}: {e}"
                utils.error(error_msg)
                raise SyncError(error_msg)


def generate_and_verify_spec(
    cwd: pathlib.Path,
    sources: dict,
):
    generate_spec.write_spec(cwd, sources)
    utils.info("generated vectors_spec.md")

    duvet_result = subprocess.run(
        ["duvet", "report", "--ci"],
        cwd=cwd,
        capture_output=True,
        text=True,
    )
    if duvet_result.returncode != 0:
        utils.error("duvet verification failed")
        utils.error(duvet_result.stderr)
        raise SyncError("duvet verification failed")
    utils.info("duvet verification passed")


def sync_sources(
    cwd: pathlib.Path,
    clone_dir: pathlib.Path,
    sources: dict,
    args: argparse.Namespace,
    using_custom_clone_dir: bool = False,
):
    # Set up directory paths that other phases depend on
    upstream_dir = cwd / "upstream"
    for source_name, source_info in sources.items():
        source_info["upstream_path"] = upstream_dir / source_name
        source_info["local_path"] = clone_dir / source_name

    if not args.skip_update:
        fetch_sources(clone_dir, sources, using_custom_clone_dir)
        update_sources(cwd, sources, args.new)
    else:
        utils.info("skipping update")

    if not args.skip_convert:
        convert_sources(cwd, clone_dir, sources)
    else:
        utils.info("skipping convert")

    if not args.skip_spec:
        generate_and_verify_spec(cwd, sources)
    else:
        utils.info("skipping spec generation")


def main() -> int:
    cwd = pathlib.Path.cwd()
    if not (cwd.parts[-1] == "vectors" and cwd.parts[-2] == "third_party"):
        print(
            f"ERROR: must run from [REPO_ROOT]/third_party/vectors, not {cwd}",
            file=sys.stderr,
        )
        return 1

    utils.info("script run from the correct directory")

    parser = argparse.ArgumentParser(
        description="Sync third-party cryptographic test vectors"
    )
    parser.add_argument(
        "--new",
        metavar="SOURCE/PATH",
        help="add new test vector file (e.g., wycheproof/testvectors_v1/aes_gcm_test.json)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify files are up-to-date without making changes",
    )
    parser.add_argument(
        "--skip-update",
        action="store_true",
        help="skip fetching and updating from upstream repositories",
    )
    parser.add_argument(
        "--skip-convert",
        action="store_true",
        help="skip converting vectors to file_test.h format",
    )
    parser.add_argument(
        "--skip-spec",
        action="store_true",
        help="skip generating vectors_spec.md and duvet verification",
    )
    parser.add_argument(
        "--clone-dir",
        metavar="DIR",
        help="use custom directory for cloned repositories (persistent across runs)",
    )
    args = parser.parse_args()

    with open("sources.toml", "rb") as f:
        sources = tomllib.load(f)

    try:
        if args.clone_dir:
            clone_dir = pathlib.Path(args.clone_dir)
            clone_dir.mkdir(parents=True, exist_ok=True)
            sync_sources(cwd, clone_dir, sources, args, using_custom_clone_dir=True)
        else:
            with tempfile.TemporaryDirectory() as temp_clone_dir:
                clone_dir = pathlib.Path(temp_clone_dir)
                sync_sources(cwd, clone_dir, sources, args)
    except SyncError as e:
        utils.error(str(e))
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())

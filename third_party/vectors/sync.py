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

from vectorslib import utils


def fetch_sources(
    tmpdir: pathlib.Path,
    sources: dict,
    skip_fetch: bool,
    using_custom_tmpdir: bool = False,
):
    if skip_fetch:
        utils.info("skipping fetch")
        return True

    for source_name, source_info in sources.items():
        stmpdir = tmpdir / source_name

        if stmpdir.is_dir():
            assert using_custom_tmpdir
            utils.warning(
                f"using existing, potentially stale upstream clone of {source_name} at {stmpdir}"
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
                    str(stmpdir),
                ],
                capture_output=True,
            )
            if ret.returncode != 0:
                utils.error(f"failed to clone {source_name}: {ret.stderr.decode().strip()}")
                return False

        assert stmpdir.is_dir()
        source_info["local_path"] = stmpdir

    return True


def update_sources(
    cwd: pathlib.Path,
    sources: dict,
    new_file: typing.Optional[str],
    skip_fetch: bool,
):
    if skip_fetch:
        utils.info("skipping update")
        return True

    upstream_dir = cwd / "upstream"
    upstream_dir.mkdir(parents=True, exist_ok=True)

    for source_name, source_info in sources.items():
        source_info["upstream_path"] = upstream_dir / source_name
        source_info["upstream_path"].mkdir(parents=True, exist_ok=True)
    
    for source_name, source_info in sources.items():
        upstream_path = source_info["upstream_path"]
        local_path = source_info["local_path"]
        
        for upstream_file in upstream_path.rglob("*"):
            if not upstream_file.is_file():
                continue
            
            relative_path = upstream_file.relative_to(upstream_path)
            local_file = local_path / relative_path
            
            if not local_file.exists():
                utils.error(f"upstream file not found in cloned repo: {source_name}/{relative_path}")
                return False
            
            if not filecmp.cmp(local_file, upstream_file, shallow=False):
                shutil.copy2(local_file, upstream_file)
                utils.info(f"updated upstream file: {source_name}/{relative_path}")

    if new_file:
        file_path = pathlib.Path(new_file)
        source_name = file_path.parts[0]
        
        if source_name not in sources:
            utils.error(f"unknown source '{source_name}', expected one of: {list(sources.keys())}")
            return False
        
        relative_path = pathlib.Path(*file_path.parts[1:])
        local_file = sources[source_name]["local_path"] / relative_path
        
        if not local_file.exists():
            utils.error(f"file not found in upstream repo: {relative_path}")
            return False
        if local_file.is_dir():
            utils.error(f"path is a directory, not a file: {relative_path}")
            return False

        upstream_file = sources[source_name]["upstream_path"] / relative_path
        if upstream_file.exists():
            utils.error(f"file already exists in upstream: {upstream_file}")
            return False

        upstream_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(local_file, upstream_file)
        utils.info(f"copied new file to upstream: {upstream_file}")

    utils.warning("update_sources isn't yet fully implemented")
    return True


def convert_sources(
    cwd: pathlib.Path,
    tmpdir: pathlib.Path,
    sources: dict,
    skip_convert: bool,
):
    if skip_convert:
        utils.info("skipping convert")
        return True

    condir = cwd / "converted"
    condir.mkdir(parents=True, exist_ok=True)
    for source_name, source_info in sources.items():
        source_info["converted_path"] = condir / source_name
        source_info["converted_path"].mkdir(parents=True, exist_ok=True)
        assert source_info["converted_path"].is_dir()

    utils.warning("convert_sources isn't yet fully implemented")
    return True


def sync_sources(
    cwd: pathlib.Path,
    tmpdir: pathlib.Path,
    sources: dict,
    new_file: typing.Optional[str],
    skip_fetch: bool,
    skip_convert: bool,
    using_custom_tmpdir: bool = False,
):
    if not fetch_sources(tmpdir, sources, skip_fetch, using_custom_tmpdir):
        return False
    if not update_sources(cwd, sources, new_file, skip_fetch):
        return False
    if not convert_sources(cwd, tmpdir, sources, skip_convert):
        return False
    return True


def main() -> int:
    cwd = pathlib.Path.cwd()
    if not (cwd.parts[-1] == "vectors" and cwd.parts[-2] == "third_party"):
        print(
            f"ERROR: must run from [REPO_ROOT]/third_party/vectors, not {cwd}",
            file=sys.stderr,
        )
        return 1

    from vectorslib import utils

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
        "--skip-fetch",
        action="store_true",
        help="skip fetching from upstream repositories",
    )
    parser.add_argument(
        "--skip-convert",
        action="store_true",
        help="skip converting vectors to file_test.h format",
    )
    parser.add_argument(
        "--tmpdir",
        metavar="DIR",
        help="use custom temporary directory for cloned repositories",
    )
    args = parser.parse_args()

    with open("sources.toml", "rb") as f:
        sources = tomllib.load(f)

    if args.tmpdir:
        tmpdir = pathlib.Path(args.tmpdir)
        tmpdir.mkdir(parents=True, exist_ok=True)
        if not sync_sources(
            cwd,
            tmpdir,
            sources,
            args.new,
            args.skip_fetch,
            args.skip_convert,
            using_custom_tmpdir=True,
        ):
            return 1
    else:
        with tempfile.TemporaryDirectory() as tmpdirname:
            tmpdir = pathlib.Path(tmpdirname)
            if not sync_sources(
                cwd, tmpdir, sources, args.new, args.skip_fetch, args.skip_convert
            ):
                return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())

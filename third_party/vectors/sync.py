#!/usr/bin/env python3

import argparse
import sys
import pathlib
import tomllib
import tempfile
import subprocess

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
                utils.error(f"failed to fetch {source_name}\n{ret.stderr.decode()}")
                return False

        assert stmpdir.is_dir()
        # Add the local path to the existing source dict
        source_info["local_path"] = stmpdir

    return True


def update_sources(
    cwd: pathlib.Path,
    tmpdir: pathlib.Path,
    sources: dict,
    skip_fetch: bool,
):
    if skip_fetch:
        utils.info("skipping update")
        return True

    updir = cwd / "upstream"
    updir.mkdir(parents=True, exist_ok=True)

    for source_name, source_info in sources.items():
        source_info["upstream_path"] = updir / source_name
        source_info["upstream_path"].mkdir(parents=True, exist_ok=True)
        assert source_info["upstream_path"].is_dir()

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
    skip_fetch: bool,
    skip_convert: bool,
    using_custom_tmpdir: bool = False,
):
    if not fetch_sources(tmpdir, sources, skip_fetch, using_custom_tmpdir):
        return False
    if not update_sources(cwd, tmpdir, sources, skip_fetch):
        return False
    if not convert_sources(cwd, tmpdir, sources, skip_convert):
        return False
    return True


def main() -> int:
    cwd = pathlib.Path.cwd()
    if not (cwd.parts[-1] == "vectors" and cwd.parts[-2] == "third_party"):
        print(
            f"ERROR: this script was run from {cwd}\nit must be run from [REPO_ROOT]/third_party/vectors",
            file=sys.stderr,
        )
        return 1

    from vectorslib import utils

    utils.info("script run from the correct directory")

    parser = argparse.ArgumentParser("Manages third-party test vectors")
    parser.add_argument(
        "--new",
        required=False,
        help="Specify new file to add as [SOURCE_NAME]/[UPSTREAM_REPO_PATH]",
    )
    parser.add_argument(
        "--check", action="store_true", help="Run checks without making any changes"
    )
    parser.add_argument(
        "--skip-fetch", action="store_true", help="Do not fetch upstream vectors"
    )
    parser.add_argument(
        "--skip-convert", action="store_true", help="Do not convert vectors"
    )
    parser.add_argument(
        "--tmpdir", required=False, help="Specify custom temporary directory"
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
            args.skip_fetch,
            args.skip_convert,
            using_custom_tmpdir=True,
        ):
            return 1
    else:
        with tempfile.TemporaryDirectory() as tmpdirname:
            tmpdir = pathlib.Path(tmpdirname)
            if not sync_sources(
                cwd, tmpdir, sources, args.skip_fetch, args.skip_convert
            ):
                return 1

    print(sources)

    if args.new:
        # copy the new file from tmpdir to upstreamdir
        utils.warning("new isn't yet implemented")

    # TODO: Implement sync logic
    return 0


if __name__ == "__main__":
    sys.exit(main())

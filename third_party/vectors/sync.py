#!/usr/bin/env python3

import argparse
import sys
import pathlib
import tomllib
import tempfile
import subprocess


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
    parser.add_argument("--new", required=False, help="Specify new file to add")
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

    def fetch_sources(tmpdir: pathlib.Path):
        if args.skip_fetch:
            utils.info("skipping fetch")
            return 0

        for source in sources:
            stmpdir = tmpdir / source

            if stmpdir.is_dir():
                assert args.tmpdir != None
                utils.warning(
                    f"using existing, potentially stale upstream clone of {source} at {stmpdir}"
                )
            else:
                ret = subprocess.run(
                    [
                        "git",
                        "clone",
                        "--branch",
                        sources[source]["branch"],
                        "--depth",
                        "1",
                        sources[source]["git_url"],
                        str(stmpdir),
                    ],
                    capture_output=True,
                )
                if ret.returncode != 0:
                    utils.error(f"failed to fetch {source}\n{ret.stderr.decode()}")
                    utils.info(ret)
                    return 1

            assert stmpdir.is_dir()
        return 0

    if args.tmpdir:
        tmpdir = pathlib.Path(args.tmpdir)
        tmpdir.mkdir(parents=True, exist_ok=True)
        ret = fetch_sources(tmpdir)
        if ret != 0:
            return ret
    else:
        with tempfile.TemporaryDirectory() as tmpdirname:
            tmpdir = pathlib.Path(tmpdirname)
            ret = fetch_sources(tmpdir)
            if ret != 0:
                return ret

    # TODO: Implement sync logic
    return 0


if __name__ == "__main__":
    sys.exit(main())

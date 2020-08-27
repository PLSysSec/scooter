#!/usr/bin/env python3

import argparse
import subprocess
from pathlib import Path
import shutil


def main() -> None:
    parser = argparse.ArgumentParser(
        description="A script for running multiple migrations "
        "on a given policy")
    parser.add_argument("policy", type=Path,
                        help="The initial policy file to use")
    parser.add_argument("migrations", nargs="+", type=Path,
                        help="The migrations to apply to the policy, in order")
    parser.add_argument(
        "--outdir", type=Path,
        help="Where to place the resulting policy files",
        default=Path("."))

    args = parser.parse_args()

    try:
        shutil.copyfile(str(args.policy), args.outdir / "policy.txt")
    except shutil.SameFileError:
        pass

    for idx, mig in enumerate(args.migrations):
        new_migpath = args.outdir / f"migration-{idx}.mig"
        shutil.copyfile(mig, new_migpath)

        result = subprocess.run(
            ["cargo", "run", "--bin",
             "migrate", "dry-run", f"migration-{idx}.mig"],
            capture_output=True,  # Capture output of command
            text=True,  # encode to a string
            cwd=args.outdir,  # Run from the script directory
            check=True)  # Fail if the exit code is non-zero

        new_migpath.unlink()

        shutil.copyfile(args.outdir / "policy.txt",
                        args.outdir / f"policy.{idx}.txt")
        with (args.outdir / "policy.txt").open('w') as f:
            print(result.stdout, file=f)

    (args.outdir / "policy.txt").rename(args.outdir /
                                        f"policy.{len(args.migrations)}.txt")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        print('Exception:')
        print('output : ' + error.output)
        print('stderr : ' + error.stderr)

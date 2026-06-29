You are repairing a broken integration test patch in AWS-LC.

Integration: INTEGRATION_PLACEHOLDER
Version/branch hint: VERSION_PLACEHOLDER
Runner script: RUNNER_SCRIPT_PLACEHOLDER
Patch directory(ies): PATCH_DIR_PLACEHOLDER (the runner may apply more than one; the failing patch may be in any of them)
Failing run: FAILING_RUN_PLACEHOLDER
Logs (last 200 lines per failed job): LOGS_DIR_PLACEHOLDER
Pre-cloned downstream source: SRC_CLONE_DIR_PLACEHOLDER (one subdirectory per downstream repo)
Repo root: SRC_ROOT_PLACEHOLDER
Write your description of changes to: DESCRIPTION_OF_CHANGES_PLACEHOLDER

The runner script is the authoritative source of truth for which downstream repo, ref, and patches are used. The version hint above may be empty or imprecise — always derive the actual ref from the runner script.

Git-based downstream repos have already been cloned for you into SRC_CLONE_DIR_PLACEHOLDER (full history, default branch). You cannot and MUST NOT clone, fetch, or pull. Work within the pre-cloned checkouts and the pre-fetched logs, and use `git checkout` inside a clone to move it to the ref the runner script uses. 
Steps:
1. Read the runner script. Identify (a) which downstream repo subdirectory under SRC_CLONE_DIR_PLACEHOLDER corresponds to it, (b) the exact ref/branch/tag/commit the test checks out (look for `git clone --branch X`, `git checkout X`, or shell variables that resolve to a ref), and (c) which patches in the patch directory are applied for that ref.
2. Read the pre-fetched logs in LOGS_DIR_PLACEHOLDER to see the exact failure (rejected hunks, build errors, etc.). Then inspect the downstream repo's recent history for context on what changed, using `git log`/`git show` in the pre-cloned checkout.
3. In the matching subdirectory under SRC_CLONE_DIR_PLACEHOLDER, `git checkout` the exact ref the runner script uses.
4. Run `patch --dry-run -p1` with the existing patches against that checkout to identify failing hunks. Only fix patches for the failing ref — do not modify patches for other refs.
5. Read the failing source context in the checkout to understand what changed upstream.
6. Author corrected patches in PATCH_DIR_PLACEHOLDER, replacing broken ones. If a hunk is redundant (upstream already does what the patch did), remove that hunk from the patch file. If an entire patch file has become redundant, remove all of its hunks so it applies as a no-op, and note in your description of changes that the file can be deleted — do not delete the file yourself.
7. Validate: re-run `patch --dry-run -p1` against a clean checkout at the correct ref (use `git checkout .` then re-checkout the ref; `git clean` is unavailable). Every patch must apply with zero fuzz and zero rejects. If validation fails, go back to step 6 until it passes.
8. Write your description of changes to DESCRIPTION_OF_CHANGES_PLACEHOLDER in GitHub-flavored markdown so it renders cleanly as a PR description. Use these three sections:

   ```
   ### Why the patch was failing
   2-4 sentences naming the broken hunk(s) and the symptom from the logs>

   ### What changed upstream
   2-4 sentences citing the upstream change and the affected lines>

   ### How I fixed it
   2-4 sentences; include a small fenced diff or `inline code` for hunk
   headers, file paths, or symbols where it makes the change concrete>
   ```

   Use `` `inline code` `` for symbols, file paths, and line refs (e.g.
   `` `vio/viosslfactories.c:488` ``). Use fenced code blocks for diffs,
   error excerpts, or commands. Keep prose tight.

Leave your corrected patch files in PATCH_DIR_PLACEHOLDER — do NOT commit, push, or open a PR; the surrounding workflow collects the changed patch files. If you cannot fix it, write a short explanation to DESCRIPTION_OF_CHANGES_PLACEHOLDER, print 'AUTOFIX_FAILED: INTEGRATION_PLACEHOLDER', and exit.

Provide a code review for the given PR. The repository name and PR number will be provided to you.

**Allowed tools:** WebFetch, Read, Glob, Grep, Agent, Bash(git *)

**Agent assumptions (applies to all agents and subagents):**
- All tools are functional and will work without error. Do not test tools or make exploratory calls.
- Only call a tool if it is required to complete the task. Every tool call should have a clear purpose.
- Do NOT use the `gh` CLI. Use `WebFetch` to fetch PR data from GitHub's public API.

**OUTPUT RULES — READ THIS FIRST:**
This command runs in `-p` (print) mode. In this mode, ONLY the main agent's direct text output is visible to the user. Subagent output, tool call results, and internal reasoning are NOT visible. Therefore:
- **YOU (the main agent) MUST write the final review as direct text in your response.** Do not delegate the final output to a subagent.
- **You MUST always produce text output.** A run that produces no text output is a failure, regardless of what happened internally.
- **If any step fails**, immediately print the error with context (which step, what URL, what error). Then either continue or explain why you cannot.
- **If you have nothing to report**, still print the review template with "No issues found."
- **Never end silently.** If you are about to finish without having printed any text, something went wrong — print a diagnostic message explaining what happened.

## Step 1: Load PR data

PR data has been pre-fetched by the CI script. Read the following files from the `.pr-data/` directory:
- `pr-metadata.json` — PR metadata (title, description, branch, state, etc.)
- `pr.diff` — the full diff
- `pr-files.json` — list of changed files

## Step 2: Gather context

Launch these in parallel:
- A haiku agent to find all relevant AIAGENT.md files (root and in directories containing modified files)
- A sonnet agent to summarize the PR changes from the diff and metadata

## Step 3: Review with parallel agents

Launch 4 agents in parallel. Each agent receives the PR title, description, diff, and list of changed files. Each returns a list of issues with descriptions and reasons.

**Agent 1 + 2: AIAGENT.md compliance sonnet agents**
Audit changes for AIAGENT.md compliance in parallel. Only consider AIAGENT.md files scoped to the modified files.

**Agent 3: Opus bug-finding agent (parallel with agent 4)**
Scan for obvious bugs. Focus only on the diff itself without reading extra context. Flag only significant bugs; ignore nitpicks and likely false positives. Do not flag issues that you cannot validate without looking at context outside of the git diff.

**Agent 4: Opus bug-finding agent (parallel with agent 3)**
Look for problems that exist in the introduced code. This could be security issues, incorrect logic, etc. Only look for issues that fall within the changed code.

This agent should read full source files (not just the diff) to understand surrounding context. Use WebFetch to fetch raw file contents from the PR branch: `https://raw.githubusercontent.com/{repo}/{branch}/{filepath}` (get the branch name from the PR metadata head ref).

### Language-Specific Checks (all review agents must apply)

**C / C++:**
- Check casts between signed/unsigned types
- Check all shift operations for undefined behavior
- Check OpenSSL/libcrypto API return values
- Check RAII/DEFER_CLEANUP ordering for stack-use-after-scope
- Check `memcmp` on secret data (should it be constant-time?)
- Early-return macro cleanup: guard macros that allocate resources must have prior allocations covered by cleanup
- Free-without-NULL: `free(ptr)` without `ptr = NULL` can cause double-free if caller also cleans up
- Ownership-transfer APIs: `set0` transfers ownership on success only; verify error paths free resources that weren't transferred

**Assembly (ARM, AArch64, x86, x86_64):**
- Verify callee-saved registers are preserved across function boundaries
- Check stack frame setup/teardown correctness
- Verify buffer accesses are bounds-checked
- Check that sensitive data is zeroed from registers and stack before return
- Verify constant-time discipline: no secret-dependent branches or memory access patterns
- Verify conditional flag usage: flags may be clobbered between the setting instruction and the conditional branch
- Register initialization on all paths when code is reordered

**Rust:**
- Check every `unsafe` block for soundness
- Check `as` casts on sizes/lengths/offsets (silent truncation)
- Check FFI lifetime correctness
- Check `unwrap()`/`expect()` reachable from untrusted input

### AI Blind Spots (all review agents must actively counter)

1. **Happy-path bias.** Bugs live on failure paths. For every function, ask "what happens when this fails?" before "what does this do?"
2. **Macro/abstraction blindness.** Guard macros (`GUARD`, `CHECK`, `ENSURE`, `BAIL`) hide control flow. Always mentally expand macros.
3. **Positive-observation bias.** Good code in one area does not imply good code everywhere in the same file.
4. **Single-function scope.** Many bugs require understanding the caller-callee contract.
5. **Cross-file context loss.** When a function calls into another file, re-read the callee's error contract.
6. **Finding-induced complacency.** After finding a bug, increase scrutiny on the rest of the file.

### CRITICAL: High signal only

Flag issues where:
- The code will fail to compile or parse
- The code will definitely produce wrong results regardless of inputs
- Clear, unambiguous AIAGENT.md violations where you can quote the exact rule
- Security vulnerabilities: memory corruption, cryptographic flaws, side-channels
- Resource leaks on error paths that are reachable

Do NOT flag:
- Pre-existing issues not introduced by this PR
- Code style or quality concerns
- Potential issues that depend on specific inputs or state
- Subjective suggestions or improvements
- Defense-in-depth suggestions ("add a redundant check just in case")
- Type-system-guaranteed safety
- API-contract-guaranteed safety where preconditions are enforced by code structure
- Unsupported-platform hypotheticals
- Linter-catchable issues
- Pedantic nitpicks a senior engineer wouldn't flag

## Step 4: Validate findings

For each issue found by agents 3 and 4, launch parallel subagents to validate:
- Each subagent gets the PR title, description, and a description of the issue
- The subagent reviews the issue to validate it with high confidence
- Use Opus subagents for bugs/logic issues, sonnet for AIAGENT.md violations
- The subagent should read the relevant source files to confirm the issue is real

Filter out any issues that were not validated.

## Step 5: Output review

Output the review as direct text in your response (see OUTPUT RULES above) in this format:

```
╔════════════════════════════════════════════════════════════════════════════════════════════════════╗
║  Code Review:                                                                                      ║
║  PR #{pr_number} - {PR title}[pad with spaces to width]                                            ║
╚════════════════════════════════════════════════════════════════════════════════════════════════════╝

┌─ Summary ──────────────────────────────────────────────────────────────────────────────────────────┐
│  {Brief description of what the PR does, wrap text to width}                                       │
└────────────────────────────────────────────────────────────────────────────────────────────────────┘

┌─ Findings ─────────────────────────────────────────────────────────────────────────────────────────┐
│                                                                                                    │
│ {For each issue, output [N] where N is the sequential number starting from 1}                      │
│ [N] {issue description with filename and line number,                                              │
│     wrap to width with proper indentation}                                                         │
│     {suggested fix if applicable}                                                                  │
│                                                                                                    │
└────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

If no issues are found, output:
```
╔════════════════════════════════════════════════════════════════════════════════════════════════════╗
║  Code Review:                                                                                      ║
║  PR #{pr_number} - {PR title}[pad with spaces to width]                                            ║
╚════════════════════════════════════════════════════════════════════════════════════════════════════╝

┌─ Summary ──────────────────────────────────────────────────────────────────────────────────────────┐
│  {Brief description of what the PR does, wrap text to width}                                       │
└────────────────────────────────────────────────────────────────────────────────────────────────────┘

┌─ Findings ─────────────────────────────────────────────────────────────────────────────────────────┐
│ ✓ No issues found. Checked for bugs, security issues, and                                          │
│   AIAGENT.md compliance.                                                                            │
└────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

# Lean 4 agent harness survey — FLT-on-Lean, bead hub-r7qdn.7

Target: K8s Job, checks out pinned Lean 4 repo (Mathlib-scale, lake-based), runs a
model in a bounded loop, must end `lake build` green. Surveyed 2026-08.

## Comparison table

| Harness | Last activity | License | Feedback granularity | K8s Job integration cost | Verdict |
|---|---|---|---|---|---|
| **leanprover-community/repl** | Active (171+ commits, ongoing agent-relevant PRs: extensibility, incremental processing, prefix-state sharing) | Apache-2.0 | Full tactic-state JSON per step (`ProofStepResponse`: goals, messages, proofStatus) via stdin/stdout JSON-RPC-ish protocol; supports `.olean` pickling of env/proofState for fast restart | Low — `lake exe repl` binary, spawn as subprocess in the Job container, pipe JSON over stdin/stdout. No server, no extra services. Needs the repl built against the *same* Mathlib toolchain commit (add as a lake dep or vendor). | Best low-level primitive; not itself a "loop," just the state channel. |
| **Pantograph (stanford-centaur/PyPantograph)** | Active, paper Oct 2024, ongoing dev branch; Apache-2.0; version pinned to a specific `lean-toolchain` per release, backports on request | Apache-2.0 | Richer than repl: metavariable-aware goal state, minimal-context exposure for search agents, tactic training-data extraction | Medium — pure-Lean core + Python bindings (`uv add git+...`), but exact Lean 4.34 pin must be verified/backported before use; adds a Python dependency layer on top of the Lean toolchain in the container image | Strong tactic-state oracle *if* the toolchain pin lines up with the FLT repo's Lean version — verify `src/lean-toolchain` before committing. |
| **LeanDojo / ReProver** | Low-maintenance research artifact — ReProver has unanswered discussions since mid-2025; org's newer energy has moved to LeanDojo-v2, TorchLean, BRIDGE (active into mid-2026) | BSD-3 (LeanDojo core) | Trace-based: extracts (state, tactic) pairs by *tracing* a full Lean project ahead of time — not a live per-iteration interactive channel in the same sense as repl/Pantograph | High — project tracing is compute- and disk-heavy, brittle across Lean/Mathlib version bumps, poor fit for a live bounded-loop Job | Skip for v0/v1; revisit only if LeanDojo-v2 (unverified maturity) displaces it. |
| **OpenHands / aider / mini-swe-agent (generic code-agent harnesses)** | All actively maintained as general coding agents; no evidence any is used for Mathlib-scale Lean specifically | MIT/Apache variants | Whatever generic shell/test feedback you wire up — no native tactic-state awareness, would just shell out to `lake build` and parse stderr | Low to adopt the harness itself, but building Lean awareness is entirely on you — equivalent to writing v0 from scratch with a heavier agent-loop framework on top | Not worth the extra layer; a bare compile-retry loop is simpler than adapting a generic SWE harness. |
| **Numina-Lean-Agent** | Active, arXiv 2601.14027 (2026); ships a full agentic toolset (`lean_goal`, `lean_diagnostic_messages`, `lean_run_code`, `lean_multi_attempt`, `lean_local_search`, `lean_loogle`) implementing a trial-feedback-optimization loop | Check repo (not independently confirmed in this pass — verify before adoption) | Live per-tool goal state + diagnostics, plus instant snippet compilation without full `lake build` | Medium — purpose-built for exactly this shape of task; needs its tool server running alongside the model in the Job, plus Mathlib/LeanDex indexing for search tools | Closest purpose-built match to the target integration; strongest v1 candidate pending a license/repo-freshness check. |
| **lean-lsp-mcp (oOo0oOo, mirrored project-numina)** | Active, PyPI-published, used in other 2026 research (Ax-Prover) | Check repo (MIT-style typical for MCP servers — verify) | Live goal state, diagnostics, hover, multi-snippet attempt-and-diagnose, external search (Loogle, Hammer, LeanSearch) via LSP — no full rebuild needed per iteration | Low-medium — `uv`-installable Python MCP server, wraps `lake serve`; needs project to already build once at image-bake time; straightforward stdio/MCP wiring into an agent loop | Best of breed for a live tactic-state oracle with minimal custom glue — top v1 pick alongside/ahead of Numina-Lean-Agent. |
| **Kimina-Prover / kimina-prover-rl (AI-MO)** | Active into 2026 (blog + arXiv 2504.11354, cited in March 2026 survey work) | Model weights on HF (Apache-2.0 typical for AI-MO releases — verify per checkpoint); training pipeline open-sourced | Not a harness per se — it's a model + RL training pipeline; interaction model is single-turn generation with **one** capped-length error-fix turn (Lean feedback injected into the prompt), not a live tactic-state loop | Medium (as a model to call, not infra) — usable as the LLM backend in your v0 loop, but its own "harness" is minimal (one retry turn only) | Interesting as the *model*, not as the interaction harness — one-shot-plus-one-fix is thinner than repl/Pantograph. |
| **DeepSeek-Prover-V2 (deepseek-ai)** | Repo last updated Jul 2025 (stale ~1yr); weights + eval scripts only | Check repo (DeepSeek license, not standard Apache/MIT — verify terms) | **No shipped interaction harness.** Repo is model weights, MiniF2F/ProverBench eval scripts, and prompting examples — no Lean REPL/LSP wrapper, no multi-turn compiler-feedback loop bundled | N/A as a harness — would need repl/Pantograph/lean-lsp-mcp bolted on regardless | **DeepSeek-native finding: none.** No DeepSeek-shipped harness fits V4 directly; use DeepSeek-Prover-V2 (or newer DeepSeek prover checkpoints) purely as the model, paired with repl or lean-lsp-mcp for the interaction layer. |

## Recommendation

**v0 (compile-retry loop):** `leanprover-community/repl`, driven directly (no Python
wrapper needed for a bounded loop) — spawn `lake exe repl` in the Job container,
feed the model's proof attempt, read back `messages`/`sorries`, retry on error,
gate final success on a real `lake build`. Lowest integration cost, Apache-2.0,
actively maintained, and it's the same primitive nearly everything else (PyPantograph
alternatives, LeanInteract) wraps anyway — cut the middleman for v0.

**v1 (tactic-state oracle):** `lean-lsp-mcp`, optionally alongside Numina-Lean-Agent's
tool patterns (`lean_multi_attempt`, `lean_goal`) for search/parallel-attempt features.
It gives live goal state and diagnostics without a full rebuild per iteration — the
key upgrade over v0's crude compile-and-parse cycle — and is already proven in an
external agent framework (Ax-Prover). Fall back to Pantograph if lean-lsp-mcp's
Lean-version tracking lags the FLT repo's pinned toolchain; Pantograph's version-pin
model is more explicit but adds a Python-binding integration step.

**Integration-cost ranking (low → high):** repl < lean-lsp-mcp ≈ Pantograph <
Numina-Lean-Agent (own tool server + indexing) < generic code-agent harnesses
(OpenHands/aider/mini-swe-agent, all glue-it-yourself for Lean) < LeanDojo/ReProver
(project-tracing overhead, low-maintenance risk).

**DeepSeek-native finding:** none — DeepSeek-Prover-V2's repo (last updated Jul 2025)
ships only model weights and eval scripts, no interaction harness. Any DeepSeek
prover checkpoint must be paired with repl (v0) or lean-lsp-mcp/Pantograph (v1)
exactly like any other model.

File: `/Users/kas/FLT/cartography/harness-survey.md`

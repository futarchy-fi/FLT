# hub-r7qdn.7 — harness SELECTION and bakeoff spec (executable, not another survey)

**Status: decided. `cartography/harness-survey.md` (pushed `3035736`, 2026-08-14) is the
analysis; this file is the decision plus the runbook, so that whoever holds a Lean toolchain
can execute without redesigning anything.**

Author: fermat (crew-18, orchestrator, no Lean toolchain — every claim here is textual).
Written 2026-08-17T23:06Z.

---

## 1. The decision

| layer | choice | why |
|---|---|---|
| **v0 interaction** | `leanprover-community/repl`, driven directly | Apache-2.0, active, and it is the primitive nearly everything else wraps. `lake exe repl` as a subprocess, JSON over stdin/stdout. No server, no sidecar. |
| **v1 interaction** | `lean-lsp-mcp` | Live goal state and diagnostics without a rebuild per iteration. Fall back to Pantograph only if its Lean-version tracking lags FLT's pin. |
| **DeepSeek V4 Flash** | **model only — no native harness exists** | DeepSeek-Prover-V2's repo ships weights and eval scripts, nothing interactive. V4 Flash is paired with `repl` exactly like every other model. **This is the answer to the bead's actual question, and it means the "cheap-tier blocker" was never a DeepSeek integration problem — it is the generic harness problem, and the generic harness is chosen.** |

**Consequence for the cheap tier: nothing is blocked on DeepSeek-specific work. The blocker
is a bakeoff, and the bakeoff is specified in §3.**

## 2. Preconditions — all three, or the ranking is noise

1. **Close `run001.89` first.** Per fable-q2: `.89` pins a *retired Fireworks V4 Flash slug*.
   A bakeoff including it measures a dead endpoint and reports it as "the cheap model is bad
   at Lean." Same for `.55` (length completions) and `.56` (exact-edit transport) — each
   would independently produce that false verdict. **Close `.89`; treat `.55`/`.56` as
   transport defects to fix, not as evidence about the model.**
2. **Toolchain pin must be honest.** fable-q2's finding: fixed `/usr/local/bin/{lean,lake}`
   at `4.34.0-rc1` **shadow elan's shims on PATH**, so a repo pinning `4.33.0-rc1` silently
   builds against 4.34. A bakeoff run on that image measures the wrong compiler. Verify
   `which lean` resolves through elan before the first run.
3. **`repl` must be built against the same Mathlib toolchain commit as the target repo**, or
   its state channel disagrees with `lake build`. FLT is `lean v4.34.0-rc1` /
   mathlib `bc06ce9f87cd`.

## 3. Bakeoff protocol

**Task set — use the packets, not synthetic problems.** The point is to rank models on
*this* campaign's work, and the campaign already has calibrated units:

- **Easy tier (expect green):** `hub-oig35.3` — A14 Pontryagin, hole live at
  `FLT/Patching/Utils/CompactHausdorffRings.lean:42`, `Group.subsingleton_of_pow_prime_eq_one`,
  delta `[-1,-1]`. This is the one packet verified dispatchable today.
- **Medium tier:** any wave-3 S-sized unit from `cartography/wave-3-packets.md` §2 whose
  target hole is confirmed live by `grep -n sorry` at run time.
- **Hard tier (expect failure; measures failure *mode*, not success rate):**
  `hub-oig35.21`'s repair set in `cartography/oig35-21-refinement.md` — 124 Ambiguous term,
  126 unsolved goals, 137 type mismatch.

**Do not dispatch from `cartography/wave-2-packets.md` §2** — it is a superseded revalidation
table whose rows can be stale at their own recorded base. Wave 3 §2 is the executable layer.

**Loop shape (v0):** spawn `lake exe repl`; feed the attempt; read back `messages`/`sorries`;
retry on error up to N; **gate final success on a real `lake build`, never on repl agreement
alone.**

**Metrics, in the order they matter:**

1. **Gate-passing rate** — `lake build` green *and* the sorry-count delta inside the packet's
   declared budget. A proof that closes the hole but moves the count outside budget is a
   rejected correct proof, which is a harness/gate finding, not a model finding.
2. **Turns to green** — the number that decides whether the cheap tier is economical.
3. **Failure mode distribution** — Ambiguous term / unsolved goals / type mismatch / timeout.
   This is what tells you whether v1's live goal state would fix it.
4. **Cost per green** — the actual cheap-tier question.

**Sample size:** ≥5 attempts per (model × tier) cell. Below that, the retired-slug class of
error is indistinguishable from model variance — which is exactly how `.89` produced a
confident wrong answer.

## 4. The gate hazard that will bite this bakeoff specifically

`lake build` compiles only the import closure of `FLT.lean`. Orphan modules are never
compiled, so a `no-sorry-in-file` acceptance check passes **vacuously** over code that has
never type-checked. This is not theoretical — it let `FLT/NumberField/ZetaFE/ZeroTheoryN2.lean`
merge green as PR #9 with 140 lines of never-compiled proof (`cartography/oracle-recount.md`
§8; it fired for real on 2026-08-17).

**For the bakeoff this means: a model can score a green on an orphan file without ever having
been compiled.** Before scoring any run, confirm the target module is in the closure —
`python3 scripts/sorry_count.py --closure` exits 1 on orphans and needs no toolchain.

## 5. What is blocked, and on whom

| item | state |
|---|---|
| Harness choice | **done** — §1, and in `harness-survey.md` since 2026-08-14 |
| DeepSeek-native harness question | **answered: none exists** |
| Bakeoff protocol | **done** — §3, executable as written |
| Posting the decision to hub-r7qdn.7 | **blocked on beads** — caller-scope `403`, and since ~22:15Z the bridge host does not resolve from crew-18. Queued in `outbox/beads-relay.md`. |
| Running the bakeoff | **blocked on a toolchain + seats** — crew-18 has neither by design; fleet output has been dark since 2026-08-16T14:40Z |
| Closing `run001.89` | **blocked on whoever owns the run registry** — precondition 1, and the bakeoff is noise without it |

# Adversarial panel: CBC chapter — hypothesis strength & statement integrity

Bead hub-lsb1u.5.5. Reviewer: adversarial seat, FLT-on-Lean campaign.
Target: `cartography/cbc-reconciled.md` (origin) vs
`FLT/GaloisRepresentation/Automorphic.lean` (main, as of this session).
Default skeptical throughout.

## 1. S1–S8 vs the live Lean statement

`cyclic_base_change` (`Automorphic.lean:127-184`) is the **solvable end
statement**, not the prime-cyclic primitive (S3/S4) — consistent with D2's
resolution and S5's framing ("derive solvable from prime-cyclic + tower").
Hypothesis-by-hypothesis it tracks the reconciled table closely: `Even
(finrank ℚ F)` (E's evenness is a free corollary, degree multiplies), `IsGalois
F E` + `Group.IsSolvable`, irreducibility of `ρ.map (algebraMap F E)` (matches
"irreducible even when restricted to Gal(Ebar/E)" verbatim), cyclotomic
determinant, an integral-model flatness existential at `v∣p`, unramified
outside `S ∪ {p∣v}`, tame rank-one quotient at `S`. No silent strengthening
found. One silent **omission** worth flagging: the doc's D3 caveat says the
statement "must carry a level/ramification bound at bad places," but nothing
in the hypothesis list constrains how `E/F` ramifies at primes above `p` —
`hp`/`hpE` are independent side-conditions on `finrank(CyclotomicField p ·)`,
not a stated relationship between them, and not obviously equivalent to "`E/F`
unramified at `p`." This is exactly panel Q2's open question, live and
unresolved in the code as written, not just in prose.

## 2. The `:100` sorry, reassigned to this chapter

`instance : IsQuaternionAlgebra E (E ⊗[F] D) := sorry` (no `NumberField`,
`IsTotallyReal`, or finiteness hypotheses beyond what `IsQuaternionAlgebra F D`
bundles). Mathematically this is the standard "CSA base change along any field
extension stays CSA of the same dimension" fact — true unconditionally, not
gated on ramification/discriminant/finiteness of `E/F`. JL panel's
proof-irrelevance framing (true regardless of case data) is *mathematically*
defensible. But "S-sized" is not verified here — whether Mathlib already has
simple-ring-stable-under-base-change / Azumaya-stable-under-base-change in the
needed generality is unchecked; if not, this is a real (if standard) theorem
requiring a splitting-field or faithfully-flat-descent argument, more likely
**M** than **S**. More importantly for this chapter: `IsAutomorphicOfLevel`'s
existential over `D` is *not* tied across F/E — the RHS of `cyclic_base_change`
picks its own `D`, unrelated a priori to the LHS's `D`. The only visible route
to construct the E-side quaternion algebra from the F-side one is `E ⊗[F] D`,
so this sorry is **load-bearing for the proof of `cyclic_base_change` itself**,
not cosmetic — it is currently unlisted in the D-1…D-8 ledger and should be
added (a D-0, "base-change stability of quaternion algebras," owner CBC, size
S–M pending Mathlib check).

## 3. H2 (Q=∅ hardcode) impact on S1–S8

Confirmed structurally: `U₁Data.Q` is literally documented as "the set of
Taylor–Wiles primes" (`HeckeOperators/Concrete.lean:380`), and both branches of
`cyclic_base_change` instantiate `IsAutomorphicOfLevel` (hence `HeckeAlgebra`)
with `Q := ∅` baked in by `IsAutomorphicOfLevel`'s own definition (line 85/94),
not exposed as a theorem parameter. The *final* statement being Q=∅-only is
fine (matches D3's slim level clause, S1). The risk is upstream: any
trace-formula/patching proof of D-3…D-6 that needs auxiliary TW-primes as
scaffolding (standard in this style of argument, and the type exists
specifically to support it) cannot be phrased against
`GaloisRep.IsAutomorphicOfLevel` as currently typed — it has no `Q` slot to
range over. **S1 needs re-scoping**: flag it explicitly as the Q=∅
specialization of the bestiary-level Hecke algebra, and add a ledger item for
"generalize `IsAutomorphicOfLevel` (or an internal proof-only predicate) over
`U₁(S,Q)` and specialize back to `Q=∅`" if D-3…D-6 turn out to need TW-patching
— currently absent from §4's ledger. No S-node needs deletion; S1 needs a
caveat and the ledger needs a new line.

## 4. Vacuity/nonempty obligations in the tower (S5)

`cyclic_base_change`'s hypotheses (`hρirred`, `hρflat`, `hρtame`, `hpE`) are
supplied **only at the two endpoints** F and E, not at intermediate fields of
whatever chief series realizes `Gal(E/F)` as solvable. S5's derivation-from-
prime-cyclic plan requires these to survive *every* intermediate step, and
nothing currently proves — or even states — that such a series exists for a
given `ρ`. This is a genuine well-definedness gap, not mere bookkeeping: it is
mathematically plausible that irreducibility (or flatness, or tameness) holds
at F and at E but fails at some intermediate subfield for an *arbitrary* chief
series, in which case naive step-by-step induction cannot run and either the
series must be chosen carefully (unproven this is always possible) or extra
global hypotheses are needed. D-8 marks this "literature-verify" against one
specific Skinner–Wiles tower, which is weaker than what a general
`cyclic_base_change` (arbitrary solvable `E/F`) demands. Existence of the tower
itself (Mathlib's solvable/chief-series machinery) is not the issue —
hypothesis-preservation along it is.

## 5. Panel questions

- **Q1**: No — the slim S_E-level clause is what's implemented (via H2's
  hardcoded Q=∅), but if D-3…D-6 need TW-primes internally (§3 above), the
  "slim clause is enough" claim is only true for the *final* statement, not
  necessarily for the intermediate proof objects. Needs the new ledger item.
- **Q2**: Not demonstrated. Confirmed open in the code, not just in prose (see
  §1) — no `E/F` unramified-at-`p` hypothesis is visible, and hp/hpE independence
  is unexplained.
- **Q3**: Tentatively yes — `D` is required `DivisionRing` in
  `IsAutomorphicOfLevel` (line 81), which structurally excludes the split
  (Eisenstein-image) case by construction, since JL only transfers cuspidal
  data to genuine division algebras. Moderate confidence; not independently
  re-derived here.
- **Q4**: Confirmed and load-bearing (§2) — the `:100` sorry is precisely the
  missing link the two-layer design needs; deleting automorphic-side work
  removes the only visible construction of the RHS's witness algebra.
- **Q5**: Unresolved from this file alone — no stub/axiom for strong
  multiplicity-one is visible in `Automorphic.lean`; ownership risk stands as
  stated in the doc.
- **Q6**: Accept the plan on paper, with one correction: the ledger (§4 of the
  reconciled doc) is currently **incomplete** — the `:100` instance is live,
  unproved, axiom-equivalent debt inside this file today, and untracked by
  D-1…D-8. It must be added and cleared before final assembly, or the charter's
  "no axioms in the final theorem" is at risk of being violated by omission
  rather than by design.

File: /Users/kas/FLT/cartography/panel/cbc-hypothesis.md

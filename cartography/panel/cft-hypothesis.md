# CFT panel seat — HYPOTHESIS STRENGTH / tame-hack certification gate (bead hub-lsb1u.9.5)

Reviewer: adversarial panel seat, FLT-on-Lean campaign. Default skeptical. Ground truth
re-derived directly from `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:150-220`,
its two consumers, and `FLT/GaloisRepresentation/Automorphic.lean:100-184`, cross-read against
`cartography/cft-reconciled.md` (origin/cartography/cft-reconciled, node 1 / §2.1 / Q2).

## 1. What the hack substitutes for the honest definition

`localTameAbelianInertiaGroup v` (`AbsoluteGaloisGroup.lean:178-184`) is defined as the
pointwise stabilizer in `Γ Kᵥ` of `S = {x | x^(q-1) ∈ fixedField(localInertiaGroup v)}`
(`q = Nat.card κ 𝒪ᵥ`). I re-derived what this field-theoretic characterization actually
computes:

- Every `y ∈ Kᵘʳ` decomposes as `ϖ^k·u`; since `Kᵘʳ` is Henselian and `q-1` is coprime to the
  residue characteristic, units of `Kᵘʳ` already have `(q-1)`-th roots in `Kᵘʳ`, so the only
  new elements `S` contributes are `(q-1)`-th roots of the uniformizer, and — because that
  divisibility fact is independent of which uniformizer is picked — the fixed field of `S` is
  exactly `Kᵘʳ(ϖ^{1/(q-1)})`, **independent of the choice of `ϖ`**. This part is not cheating;
  it is a clean, uniformizer-free local statement.
- `Gal(Kᵘʳ(ϖ^{1/(q-1)})/Kᵘʳ) ≅ μ_{q-1}(κ) = κ^×` via Kummer theory (`σ ↦ σ(x)/x mod 𝔪`), and
  the composite `I_v ↠ Gal(Kᵘʳ(ϖ^{1/(q-1)})/Kᵘʳ)` is exactly **Serre's fundamental/tame
  character of level 1**, `ω: I_v → κ(v)^×`. So `localTameAbelianInertiaGroup v = ker(ω)` as a
  subgroup of `Γ Kᵥ` — **this is the honest definition, reached via Iwasawa/tame-Kummer theory
  alone, no local or global CFT**, matching the reconciled map's routing (M-sized,
  unramified + Kummer, `KummerExtension` + ramification files).
- **The substitution is NOT `ker(ω)` vs. "something wrong"** — it is `ker(ω)` (finite level-1
  truncation, index `q-1` in `I_v/P_v`) **standing in, unproven, for what the docstring's own
  "TODO: show this is the right group" implicitly worries is the full tame quotient kernel**
  `P_v` (wild inertia, `= ker(I_v ↠ I_v/P_v ≅ ∏_{ℓ≠p} ℤ_ℓ)`). These two candidate "right
  groups" are **not equal**: `T := I_v/P_v` is an infinite procyclic pro-(p′) group, and
  `T ↠ T/(q-1)T ≅ κ^×` is a proper, infinite-index-in-the-other-direction quotient, so
  `ker(ω) ⊋ P_v` strictly, always (`T` has ℓ-adic factors for every prime `ℓ ≠ p`, most of
  which don't divide `q-1`).

## 2. Direction of the gap, and the false-instantiation question

Because `hρtame` in `cyclic_base_change` is stated as `localTameAbelianInertiaGroup w ≤ δ.ker`
(`Automorphic.lean:176`), and `ker(ω) ⊋ P_v`, the **hack's hypothesis is strictly stronger**
(harder for `δ` to satisfy) than the textbook "tamely ramified" condition `P_w ≤ δ.ker`. A
theorem proved under a strictly stronger hypothesis cannot become false by that substitution —
it can only become **too narrow to invoke** (vacuous on `δ` of order coprime to `q_w - 1`).

**I looked for, and did not find, a false-instantiation scenario in this direction.** Any `δ`
satisfying the FLT hypothesis (`ker(ω) ≤ δ.ker`) is automatically tame in the textbook sense
(`P_w ≤ ker(ω) ≤ δ.ker`), so any classical proof of cyclic base change under "genuine tameness"
already covers every instance the FLT-formalized hypothesis can produce. **The transmission
risk the reconciled map graded "medium and rising" is real as an *engineering/usability* risk
(the axiom may be too narrow to discharge real automorphic `ρ`'s whose tame quotient has order
not dividing `q_w-1`) but is not a *soundness* risk** given the direction of the gap.

Caveat that keeps this from being a clean bill of health: this whole argument **assumes** the
field-theoretic characterization really does equal `ker(ω)` and nothing coarser — that
equivalence is exactly the open TODO, unverified in Lean. A slip in the Kummer-divisibility
argument (e.g. if `Kᵘʳ`-unit-divisibility silently fails at `p=2`, `q=2`, or if `S` picks up
extra ramified elements I didn't account for) could in principle make the def *smaller* than
`ker(ω)` — possibly as small as `P_v` or even a proper subgroup of it — which **would** flip
the direction and reopen a genuine false-instantiation risk. I checked the `q=2` edge case by
hand (§1 derivation degenerates correctly to `localTameAbelianInertiaGroup = I_v` when
`κ^×` is trivial) and found no problem, but this was hand verification, not a Lean proof — it
is exactly the gap the certification lemma must close.

There is a second, independent reason to expect `ker(ω)` (not `P_v`) is in fact the
*mathematically intended* object here, which somewhat vindicates the original author's choice:
`cyclic_base_change`'s conclusion is stated for `IsAutomorphicOfLevel ... S` — **U₁(S)-level**
automorphic forms, and classical U₁(𝔭)-level structure is indexed precisely by characters of
`(O_F/𝔭)^× = κ(w)^×`, i.e. exactly the level-1 truncation `ker(ω)`, not the full wild-inertia
kernel. So the "cheating" may be cheating only in the sense of being unproved, not in the
sense of being the wrong target.

## 3. Certification criterion

**Lemma to prove:** `localTameAbelianInertiaGroup v = ker (tameCharacter v)`, where
`tameCharacter v : I_v →* κ(v)^×` is independently constructed as the standard Kummer
character (`σ ↦ σ(ϖ^{1/(q-1)}) / ϖ^{1/(q-1)}` under the Kummer/`IsPrimitiveRoot`
identification `Gal(Kᵘʳ(μ_{q-1}-th root of ϖ)/Kᵘʳ) ≅ μ_{q-1}(κ)`), together with
uniformizer-independence of that construction. This is the natural certifying statement:
it pins the hack to a definition built by the standard route (unramified base change + Kummer
theory for the cyclic degree-`(q-1)` extension), rather than to the ad hoc fixed-field
description, closing the "TODO" honestly instead of leaving it as folklore.

**Size: M**, agreeing with the reconciled map, with one refinement: the bulk of the M is not
"identify the right group" (§1 above already pins it down mathematically) but **formalizing
the uniformizer-independence step** (units of `Kᵘʳ` are `(q-1)`-divisible, via Hensel + the
residue field already containing `μ_{q-1}`) and **wiring a `KummerExtension`/Kummer-theory
API for a genuinely infinite/profinite base (`Kᵘʳ`, not a number field)** — check whether
FLT's or Mathlib's Kummer theory files are stated at the generality needed for `Γ Kᵥ`
directly, or need a finite-level unfolding through `IsGalois`/`fixedField` machinery already
used at `AbsoluteGaloisGroup.lean:167-168`. If the Kummer API only exists for finite
extensions, the lemma needs a colimit/direct-limit argument over finite unramified pieces of
`Kᵘʳ`, which would push this toward the L end of M rather than S end.

## 4. Panel questions (this lens)

1. **Export contract:** not this lens's call — CFT-bead-external question, no bearing on the
   tame hack (node 1 needs no CFT export either way).
2. **Tame-inertia certification gate — ratify, with a refinement to the ratification
   itself:** yes, land the certification lemma (§3) before `cyclic_base_change` moves from
   `sorry` to `knownin1980s`/axiom — but not because the current def risks a false axiom (§2
   argues the risk, if it materializes, would make the axiom *too narrow*, not false). Ratify
   it because (a) an unverified "TODO: is this the right group" sitting under a permanent
   axiom is an unacceptable process norm regardless of which direction the risk points, and
   (b) I cannot fully rule out the direction-flip caveat in §2 without the Lean proof — the
   hand-verification is not a certification. Owner: whoever holds
   `AbsoluteGaloisGroup.lean` (Deformations/RepresentationTheory) — no current owner is named
   in the file; this should be assigned, not left implicit.
3. **SW-trick axiom shape / Frobenius sign:** out of scope for this lens except to note (§2)
   that arithmetic-vs-geometric Frobenius sign flips do **not** threaten `hρtame` specifically,
   since `ker(ω) = ker(ω^{-1})` — the `≤ δ.ker` hypothesis is sign-invariant. Sign risk is
   confined to wherever `adicArithFrob` (not this def) is consumed directly.
4. Not this lens.
5. Not this lens.
6. **Brauer/quaternion watch-item:** not this lens; note only that `Automorphic.lean:100`
   (`sorry` on `IsQuaternionAlgebra`) sits structurally close to but does not interact with
   the tame-hack path (`:176`) — different hypotheses of the same file, not a shared risk.

## 5. Bottom line

Gate verdict: **ratify the certification-before-axiomatization gate, but downgrade the
soundness framing.** The reconciled map's "medium and rising, becomes a false axiom" language
overstates the soundness exposure given the direction of the gap I traced (`ker(ω) ⊋ P_v`
makes the formalized hypothesis stronger, not weaker, than textbook tameness) — the more
accurate framing is "kernel-checked def, unverified identity, and the failure mode most in
evidence is *too-narrow-to-use*, with a residual, currently-unexcluded *soundness* risk
if the uniformizer-independence step turns out to be wrong." Both failure modes are killed by
the same certification lemma, so the practical recommendation (land node 1 before the axiom)
is unchanged.

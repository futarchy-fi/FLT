/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.CyclicBaseChange.Satake
public import FLT.GaloisRepresentation.Automorphic

/-!
# Cyclic base change for GL(2): the statement layer

This file is the statement layer of the cyclic-base-change chapter, cartography nodes
**S1–S4** of `cartography/cbc-reconciled.md` §5/§7 as repaired by
`cartography/panel/cbc-adjudication.md`.  Nothing here is proved; the four proof
obligations that remain open carry the ledger tags recorded below.

The substrate is the *quaternionic* one, per the reconciliation's divergence D7: totally
definite quaternion algebras over totally real fields, weight two, trivial central
character, in the shape already built in `FLT/AutomorphicForm/QuaternionAlgebra/` and
`FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean`.  A *Hecke
eigensystem* is, exactly as in `GaloisRep.IsAutomorphicOfLevel`
(`FLT/GaloisRepresentation/Automorphic.lean`), a `ℤ_[p]`-algebra map out of
`TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮`.  Trivial central character is not a
hypothesis here because it is part of `WeightTwoAutomorphicForm` itself.

## Main definitions

* `CyclicBaseChange.SatakeParam.trace`, `CyclicBaseChange.SatakeParam.det` — the two
  symmetric functions of an unramified rank-two Satake parameter (node S2, whose norm map
  `SatakeParam.norm` already lives in `FLT/CyclicBaseChange/Satake.lean`).
* `CyclicBaseChange.IsSatakeParamAt` — the Satake/Hecke interface (node S1): `a` is the
  unramified Satake parameter of the eigensystem `π` at the good place `v`.
* `CyclicBaseChange.IsBaseChangeSatake` — the Satake compatibility `α_w = α_v ^ f(w/v)`
  relating an eigensystem over `F` to one over `E` (nodes S3/S4, local scope fixed by
  divergences D3/D4).
* `CyclicBaseChange.IsGaloisInvariantSatake` — σ-invariance of an eigensystem over `E`,
  expressed at the Satake level: the Hecke eigenvalue at `w` depends only on `w ∩ 𝓞 F`.
* `CyclicBaseChange.IsUnramifiedAtPrimesAbove` — the `E/F`-unramified-at-`p` side
  condition, made explicit in code per the panel's statement repair (open question PQ2).

## Main statements

* `CyclicBaseChange.exists_isSatakeParamAt` (S1) — over an algebraically closed
  coefficient field every good place has a Satake parameter.
* `CyclicBaseChange.exists_baseChange` (S3) — existence of `BC_{E/F}(π)` for prime-cyclic
  totally real `E/F`, with norm-Satake compatibility and σ-invariance.
* `CyclicBaseChange.exists_of_isGaloisInvariantSatake` (S4) — descent: a σ-invariant
  eigensystem over `E` is a base change.
* `CyclicBaseChange.exists_character_of_isBaseChangeSatake` (S4, fiber clause) — the fiber
  of base change is a torsor under characters of `Gal(E/F)`.

Reference for S3/S4: R. P. Langlands, *Base Change for GL(2)*, Annals of Mathematics
Studies 96, Princeton University Press (1980), Chapter 1, Properties **B** (existence and
local compatibility of the lifting) and **C** (characterisation of the image by
σ-invariance, with the fiber a torsor under `Gal(E/F)^`).  The reference for the
Satake/norm bookkeeping at unramified places is the same chapter's §1 norm map.

## Scope: what is deliberately absent

* **S5 (solvable-from-prime-cyclic tower) is out of scope for this file**, and so is
  **S6 (automorphic induction from a quadratic CM field)**.  See the ledger entry
  D-8E/D-8P below and, in particular, the post-1990 literature dependency recorded there.
* Ramified local base change (Shintani character identities) is out of the statement by
  divergence D3 of `cbc-reconciled.md`; only the unramified Satake clause and a level
  bound appear.  The proof obligation is ledger item D-2.
* The Eisenstein/non-cuspidal edge case (panel question PQ3) is tentatively resolved
  structurally: the substrate demands `[DivisionRing D]`, i.e. a genuine totally definite
  quaternion algebra, whose automorphic spectrum carries no Eisenstein part.  No
  cuspidality hypothesis is therefore imposed in S3/S4.

## TODO (statement-layer, tracked elsewhere)

Reconciliation item §7.6 asks for the existing Galois-side interface `cyclic_base_change`
(`FLT/GaloisRepresentation/Automorphic.lean`, the finite-solvable statement) to record two
things in its own docstring, which this packet may not edit:

* **D3's level-bound reading.**  `cyclic_base_change` pulls the level `S` back along
  `HeightOneSpectrum.preimageComapFinset` and asserts automorphy of level exactly `S_E`.
  Divergence D3 of `cbc-reconciled.md` reads the Langlands statement as the weaker "the
  level of `BC(π)` *divides* the pullback `S_E`", i.e. `BC(π)` is unramified wherever both
  `π` and `E/F` are.  The two readings agree for the square-free `U₁(S)` levels used in
  FLT, but the slim divides-clause is what the eventual proof supplies; the equality form
  is what `Automorphic.lean` consumes.  This file states the compatible equality form
  (`hlevel` below) and flags the discrepancy as a TODO on the Galois-side interface.
* **Panel question Q2's ramification side condition.**  `cyclic_base_change` currently
  carries no hypothesis that `E/F` is unramified at `p`; PQ2 is confirmed open, so that
  side condition is a TODO hypothesis there.  Here it is explicit as
  `IsUnramifiedAtPrimesAbove`.

## Deferred-obligation ledger (D-1 … D-10)

`cbc-reconciled.md` §4 plus the D-9/D-10 rows added by `panel/cbc-adjudication.md`.
Every entry must eventually be proved; the campaign charter forbids any of them surviving
as an axiom into the final theorem.  "Owner" is the hub that proves it; CBC consumes.

**D-1** (owner: shared JL/CBC, JL hub leads; size L; discharges S1, S3).
Local GL₂ representation theory sufficient for parameters and Satake data: principal
series, special, supercuspidal.  Bushnell–Henniart; Langlands 1980, local chapters.

**D-2** (owner: CBC; size L; discharges S3, S4).
Local cyclic base change / Shintani lifting: the norm map on conjugacy classes, the
character identities, ramified and archimedean places in the weight-two class.  Out of the
statement by divergence D3, required by the proof.  Shintani 1979; Langlands 1980.

**D-3** (owner: JL hub, shared; size XL; discharges S3, S4).
Measures, adelic quotients, orbital integrals, and matching of test functions `GL₂(F_v)`
against `GL₂(E_w)`, including fundamental-lemma-type identities for cyclic GL₂.
Langlands 1980 chs. 2–3; Labesse, Astérisque 257; Arthur 2005.

**D-4** (owner: JL hub, shared; size XL; discharges S3, S4).
Twisted trace formula for GL₂ (the `Gal(E/F)`-twist): geometric and spectral sides,
truncation, convergence; plus the untwisted formula the JL hub already needs.
Langlands 1980 chs. 6–11; Saito 1975; Arthur–Clozel 1989 ch. 3.

**D-5** (owner: CBC, multiplicity one: JL; size XL, multiplicity one M/L; discharges S3,
S4 and the level-bound clause).
Spectral comparison giving existence of `BC_{E/F}(π)` with the expected Satake data, the
level bound, and the cuspidality dichotomy; strong multiplicity one for GL₂ and its inner
forms.  Langlands 1980 main theorem; Jacquet–Shalika.

**D-6** (owner: CBC; size L; discharges S4).
The descent/image theorem: a σ-invariant cuspidal `Π` descends, the fiber is a torsor
under the characters of `Gal(E/F)`, and the Eisenstein edge case is excluded or handled.
Langlands 1980, descent chapters.

**D-7** (owner: CBC, consumed by the Galois-representations hub; size L–XL; discharges S6).
Automorphic induction: theta-series / Weil-representation or converse-theorem construction
of `AI_{K/F}(χ)` with local compatibility.  Independent of the trace-formula stack.
Hecke 1926; Jacquet–Langlands ch. 12; Arthur–Clozel 1989.

**D-8E** (owner: CBC; size M; discharges S5).
Admissible-tower existence: choose a prime-cyclic tower `F = F₀ ⊂ … ⊂ Fₙ = E` on which
every intermediate restriction satisfies the hypotheses the next S3/S4 step needs.

**D-8P** (owner: CBC; size M; discharges S5 and D-8E).
Tower preservation: irreducibility of the restriction, flatness at `v ∣ p`, the tame
rank-one quotient at `S`, and linear disjointness survive each prime-cyclic stage.

**D-9** (owner: CBC; size S–M; discharges S3, S4).
The `Q = ∅` hardcode (JL panel finding H2).  Pinning the final statement to the `Q = ∅`
specialization is acceptable only if it is caveated in code — see the comment above
`exists_baseChange` below — and only if patching-side sufficiency is proved by whoever
pins it.

**D-10** (owner: CBC; size M; discharges S3, S4).
The central-simple-algebra base-change instance in `FLT/GaloisRepresentation/Automorphic`
(`IsQuaternionAlgebra E (E ⊗[F] D)`) is proof-load-bearing: it is the only visible route
to the witness algebra over `E`.  It is M-sized, not S, and was untracked.  Until it is
tracked, this file takes the quaternion algebra `DE` over `E` as *given data* rather than
as `E ⊗[F] D`.

### Prominent: the tower step (S5) has a post-1990 literature dependency

The panel's sustained refutation (adjudication, "Refutation sustained (literature)") is
that iterating the prime-cyclic case up a solvable tower is **not** free.  The descent step
in the tower requires

* C. S. Rajan, *On the image and fibres of solvable base change*, Math. Res. Lett. 9
  (2002), and
* L. Clozel and C. S. Rajan, *Solvable base change and Galois descent* (2021), whose
  Theorem 2 is the Lapid–Rogawski criterion.

Both are **post-1990**.  The campaign charter does not require 1980s purity, but honesty
about the dependency does: any claim that the CBC chapter rests only on Langlands (1980)
is false at the tower step.  S5 is consequently resized upward (D-8E/D-8P) and is **not**
stated in this file.

The second, independent S5 gap recorded by the panel is *vacuity*: the induction has no
existence claim that a chief series preserving the endpoint hypotheses (irreducibility,
flatness, tameness) exists — the hypotheses are supplied only at the `F` and `E`
endpoints.  Deriving an admissible tower from the endpoint hypotheses is D-8P and must not
be smuggled into a group-theoretic chief-series lemma.

Two further panel outcomes are recorded for the record: S7 (the Skinner–Wiles CFT trick)
was repriced M → L, and PQ5 (who owns strong multiplicity one if the JL hub descopes it)
is assigned to the Galois-representations chapter's G-schema at statement time.
-/

@[expose] public section

open IsDedekindDomain NumberField TotallyDefiniteQuaternionAlgebra WeightTwoAutomorphicForm
open IsQuaternionAlgebra.NumberField

namespace CyclicBaseChange

/-!
## S2: the symmetric functions of a Satake parameter

The norm map `SatakeParam.norm` itself is in `FLT/CyclicBaseChange/Satake.lean`.  What the
Hecke side actually sees is the pair (trace, determinant), so we name them and record how
they interact with the norm: the determinant is multiplicative and the traces of the
successive norms satisfy the rank-two Newton recursion.  That recursion is the algebraic
content of "`α_w = α_v ^ f` turns into a relation between `T_w` and `T_v` eigenvalues".
This is all pure algebra; no proof obligation from the ledger is involved.
-/

namespace SatakeParam

variable {R : Type*}

/-- The trace `α + β` of a rank-two Satake parameter. -/
def trace [Add R] (a : SatakeParam R) : R := a.first + a.second

/-- The determinant `α * β` of a rank-two Satake parameter. -/
def det [Mul R] (a : SatakeParam R) : R := a.first * a.second

@[simp] theorem trace_mk [Add R] (x y : R) : trace ⟨x, y⟩ = x + y := rfl

@[simp] theorem det_mk [Mul R] (x y : R) : det ⟨x, y⟩ = x * y := rfl

@[simp]
theorem norm_one [Monoid R] (a : SatakeParam R) : a.norm 1 = a := by
  cases a; simp [norm]

/-- The Satake norm is multiplicative in the residue degree; this is what makes the
unramified clause of S3 compose along a tower (cf. `Ideal.inertiaDeg_tower`). -/
theorem norm_norm [Monoid R] (f g : ℕ) (a : SatakeParam R) :
    (a.norm f).norm g = a.norm (f * g) := by
  simp [norm, pow_mul]

@[simp]
theorem det_norm [CommMonoid R] (f : ℕ) (a : SatakeParam R) :
    (a.norm f).det = a.det ^ f := by
  simp [norm, det, mul_pow]

/-- The rank-two Newton recursion for the traces of the successive Satake norms:
`α^{f+2} + β^{f+2} = (α+β)(α^{f+1} + β^{f+1}) - αβ(α^f + β^f)`. -/
theorem trace_norm_add_two [CommRing R] (f : ℕ) (a : SatakeParam R) :
    (a.norm (f + 2)).trace = a.trace * (a.norm (f + 1)).trace - a.det * (a.norm f).trace := by
  simp only [norm, trace, det]
  ring

end SatakeParam

/-!
## S1: the Satake/Hecke interface

Node S1, downgraded to size S by the adjudication because the quaternionic Hecke substrate
it sits on is already complete.  For a weight-two eigensystem of trivial central character
and a place `v` good for the level, the Satake parameter at `v` is the unordered pair of
roots of `X² - π(Tᵥ) X + N(v)`.  Existence over an algebraically closed coefficient field
is the S1 obligation; it is backed by D-1.
-/

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
variable {p : ℕ} [Fact p.Prime]
variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A]

/-- `a` is an unramified Satake parameter of the weight-two quaternionic Hecke eigensystem
`π` at the place `v`, which is good for the level `𝒮`: its trace is the `Tᵥ`-eigenvalue of
`π` and its determinant is the absolute norm `N(v)` (the weight-two, trivial-central-
character normalisation, matching `GaloisRep.IsAutomorphicOfLevel`).

The parameter is only ever determined as an unordered pair; see `IsSatakeParamAt.swap`. -/
def IsSatakeParamAt
    (D : Type*) [DivisionRing D] [Algebra F D] [WithRigidification F D]
    (𝒮 : U₁Data F ℤ_[p] p)
    (π : HeckeAlgebra (R := ℤ_[p]) D 𝒮 →ₐ[ℤ_[p]] A)
    (v : HeightOneSpectrum (𝓞 F)) (hvS : v ∉ 𝒮.S) (hvQ : v ∉ 𝒮.Q)
    (a : SatakeParam A) : Prop :=
  a.trace = π (HeckeAlgebra.T (R := ℤ_[p]) D 𝒮 v hvS hvQ) ∧
  a.det = (v.asIdeal.absNorm : A)

omit [IsTotallyReal F] in
/-- Satake parameters are unordered pairs. -/
theorem IsSatakeParamAt.swap
    {D : Type*} [DivisionRing D] [Algebra F D] [WithRigidification F D]
    {𝒮 : U₁Data F ℤ_[p] p}
    {π : HeckeAlgebra (R := ℤ_[p]) D 𝒮 →ₐ[ℤ_[p]] A}
    {v : HeightOneSpectrum (𝓞 F)} {hvS : v ∉ 𝒮.S} {hvQ : v ∉ 𝒮.Q}
    {a : SatakeParam A} (h : IsSatakeParamAt D 𝒮 π v hvS hvQ a) :
    IsSatakeParamAt D 𝒮 π v hvS hvQ ⟨a.second, a.first⟩ :=
  ⟨by simpa [SatakeParam.trace, add_comm] using h.1,
    by simpa [SatakeParam.det, mul_comm] using h.2⟩

/-- **S1 (Satake/Hecke interface).**  Over an algebraically closed coefficient field every
place `v` good for the level carries a Satake parameter for the eigensystem `π`: the pair
of roots of `X² - π(Tᵥ) X + N(v)`.  Ledger: D-1. -/
theorem exists_isSatakeParamAt
    {K : Type*} [Field K] [Algebra ℤ_[p] K] [IsAlgClosed K]
    (D : Type*) [DivisionRing D] [Algebra F D] [WithRigidification F D]
    (𝒮 : U₁Data F ℤ_[p] p)
    (π : HeckeAlgebra (R := ℤ_[p]) D 𝒮 →ₐ[ℤ_[p]] K)
    (v : HeightOneSpectrum (𝓞 F)) (hvS : v ∉ 𝒮.S) (hvQ : v ∉ 𝒮.Q) :
    ∃ a : SatakeParam K, IsSatakeParamAt D 𝒮 π v hvS hvQ a := by
  sorry

/-!
## S3/S4: base change and descent

`E/F` is a prime-cyclic extension of totally real number fields.  Per ledger item D-10 the
quaternion algebra `DE` over `E` is taken as given data rather than built as `E ⊗[F] D`:
the relevant central-simple-algebra base-change instance is load-bearing and untracked, so
no packet may rely on it silently.

Per divergences D3/D4 the only local content in the statements is the unramified Satake
clause `α_w = α_v ^ f(w/v)` together with the level bound; ramified local base change is
ledger item D-2 and is not visible here.
-/

variable {E : Type*} [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E]

/-- The unramified Satake compatibility relating an eigensystem `π` over `F` to an
eigensystem `Pi` over `E`: at every place `w` of `E` good for the level over `E` and lying
over a place `v` of `F` good for the level over `F`, the Satake parameter of `Pi` at `w` is
the norm `SatakeParam.norm` of the parameter of `π` at `v`, taken to the residue degree
`f(w/v) = Ideal.inertiaDeg`.  This is Langlands, AM-96, Ch. 1, Property B. -/
def IsBaseChangeSatake
    (D : Type*) [DivisionRing D] [Algebra F D] [WithRigidification F D]
    (DE : Type*) [DivisionRing DE] [Algebra E DE] [WithRigidification E DE]
    (𝒮 : U₁Data F ℤ_[p] p) (𝒮E : U₁Data E ℤ_[p] p)
    (π : HeckeAlgebra (R := ℤ_[p]) D 𝒮 →ₐ[ℤ_[p]] A)
    (Pi : HeckeAlgebra (R := ℤ_[p]) DE 𝒮E →ₐ[ℤ_[p]] A) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 E)) (hwS : w ∉ 𝒮E.S) (hwQ : w ∉ 𝒮E.Q)
    (hvS : HeightOneSpectrum.under (𝓞 F) w ∉ 𝒮.S)
    (hvQ : HeightOneSpectrum.under (𝓞 F) w ∉ 𝒮.Q)
    (a : SatakeParam A),
    IsSatakeParamAt D 𝒮 π (HeightOneSpectrum.under (𝓞 F) w) hvS hvQ a →
    IsSatakeParamAt DE 𝒮E Pi w hwS hwQ (a.norm (w.asIdeal.inertiaDeg (𝓞 F)))

/-- σ-invariance of an eigensystem over `E`, expressed at the Satake level: since
`Gal(E/F)` permutes the places of `E` above a place of `F` transitively, invariance of
`Pi` under `Gal(E/F)` is the statement that its Hecke eigenvalue at a good place `w`
depends only on the place `w ∩ 𝓞 F` of `F` below it.  This is the hypothesis side of
Langlands, AM-96, Ch. 1, Property C.

Stating invariance this way avoids having to construct the `Gal(E/F)`-action on the Hecke
algebra of `DE`, which is part of ledger item D-10. -/
def IsGaloisInvariantSatake
    (DE : Type*) [DivisionRing DE] [Algebra E DE] [WithRigidification E DE]
    (𝒮E : U₁Data E ℤ_[p] p)
    (Pi : HeckeAlgebra (R := ℤ_[p]) DE 𝒮E →ₐ[ℤ_[p]] A) : Prop :=
  ∀ (w w' : HeightOneSpectrum (𝓞 E)) (hwS : w ∉ 𝒮E.S) (hwQ : w ∉ 𝒮E.Q)
    (hwS' : w' ∉ 𝒮E.S) (hwQ' : w' ∉ 𝒮E.Q),
    HeightOneSpectrum.under (𝓞 F) w = HeightOneSpectrum.under (𝓞 F) w' →
    Pi (HeckeAlgebra.T (R := ℤ_[p]) DE 𝒮E w hwS hwQ) =
      Pi (HeckeAlgebra.T (R := ℤ_[p]) DE 𝒮E w' hwS' hwQ')

variable (F E) in
/-- `E/F` is unramified at `p`: every place of `E` above `p` has ramification index one
over `F`.

The panel's statement repair requires this side condition to be visible **in code**, not
only in prose: panel question Q2 (does some stage of the Skinner–Wiles tower need `E/F`
unramified at `p`?) is confirmed open, and the Galois-side interface `cyclic_base_change`
in `FLT/GaloisRepresentation/Automorphic.lean` currently omits it. -/
def IsUnramifiedAtPrimesAbove : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 F) = 1

-- D-9 (Q = ∅ caveat).  The hypotheses `hQ`/`hQE` below pin both level data to the
-- `Q = ∅` specialization, i.e. no Taylor–Wiles primes.  That is exactly the shape
-- `GaloisRep.IsAutomorphicOfLevel` hardcodes (it instantiates `U₁Data` with `Q := ∅`), and
-- it is what the two blueprint consumers of cyclic base change need.  It is NOT the
-- general statement: base change for levels with `Q ≠ ∅` needs the Taylor–Wiles auxiliary
-- primes to split or stay inert compatibly in `E/F`, and the patching-side sufficiency of
-- the `Q = ∅` specialization has not been proved.  Whoever removes these hypotheses owes
-- that argument; until then this is ledger item D-9.

/-- **S3 (existence of cyclic base change).**  Let `E/F` be a Galois extension of totally
real number fields of prime degree — hence cyclic — with `F` of even degree over `ℚ` and
`E/F` unramified at `p`.  Let `π` be a weight-two quaternionic Hecke eigensystem over `F`
of level `𝒮` with `Q = ∅`, and let `𝒮E` be a level over `E` whose bad set is the pullback
of that of `𝒮` (the D3 level bound, in its equality form).  Then `π` has a base change to
`E`: an eigensystem `Pi` of level `𝒮E` whose Satake parameters are the norms of those of
`π`, and which is `Gal(E/F)`-invariant.

Langlands, *Base Change for GL(2)*, Annals of Math. Studies 96 (1980), Ch. 1, Property B.
Ledger: D-1, D-2, D-3, D-4, D-5 (and D-9, D-10 for the hypotheses' shape).

The hypotheses are aligned with the Galois-side interface `cyclic_base_change`
(`FLT/GaloisRepresentation/Automorphic.lean`): `Even (Module.finrank ℚ F)`, a totally real
Galois `E/F`, level pulled back along `HeightOneSpectrum.preimageComapFinset`.  Where they
differ, deliberately: that statement is for finite *solvable* `E/F` (it is the S5 gluing of
this one, which this packet does not attempt) and it carries no unramified-at-`p`
condition (see `IsUnramifiedAtPrimesAbove` and the TODO in the module docstring). -/
theorem exists_baseChange [IsGalois F E]
    (hF : Even (Module.finrank ℚ F))
    (hEF : (Module.finrank F E).Prime)
    (hEFp : IsUnramifiedAtPrimesAbove F E (p := p))
    (D : Type*) [DivisionRing D] [Algebra F D] [WithRigidification F D]
    (DE : Type*) [DivisionRing DE] [Algebra E DE] [WithRigidification E DE]
    (𝒮 : U₁Data F ℤ_[p] p) (𝒮E : U₁Data E ℤ_[p] p)
    (hQ : 𝒮.Q = ∅) (hQE : 𝒮E.Q = ∅)
    (hlevel : 𝒮E.S = HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) 𝒮.S)
    (π : HeckeAlgebra (R := ℤ_[p]) D 𝒮 →ₐ[ℤ_[p]] A) :
    ∃ Pi : HeckeAlgebra (R := ℤ_[p]) DE 𝒮E →ₐ[ℤ_[p]] A,
      IsBaseChangeSatake D DE 𝒮 𝒮E π Pi ∧
      IsGaloisInvariantSatake (F := F) DE 𝒮E Pi := by
  sorry

/-- **S4 (σ-invariance descent).**  Same hypotheses on `E/F` and on the levels as S3.  A
weight-two quaternionic Hecke eigensystem `Pi` over `E` which is `Gal(E/F)`-invariant lies
in the image of base change: it is the base change of some eigensystem over `F`.

Langlands, *Base Change for GL(2)*, Annals of Math. Studies 96 (1980), Ch. 1, Property C.
Ledger: D-5, D-6 (existence of the descent) and the multiplicity-one input owned by the
Jacquet–Langlands hub, without which the descent is not well posed on eigensystems.

No cuspidality hypothesis appears: on the totally definite quaternionic substrate the
`[DivisionRing DE]` requirement structurally excludes the Eisenstein series that Langlands'
full descent has to classify (panel question PQ3, tentatively resolved). -/
theorem exists_of_isGaloisInvariantSatake [IsGalois F E]
    (hF : Even (Module.finrank ℚ F))
    (hEF : (Module.finrank F E).Prime)
    (hEFp : IsUnramifiedAtPrimesAbove F E (p := p))
    (D : Type*) [DivisionRing D] [Algebra F D] [WithRigidification F D]
    (DE : Type*) [DivisionRing DE] [Algebra E DE] [WithRigidification E DE]
    (𝒮 : U₁Data F ℤ_[p] p) (𝒮E : U₁Data E ℤ_[p] p)
    (hQ : 𝒮.Q = ∅) (hQE : 𝒮E.Q = ∅)
    (hlevel : 𝒮E.S = HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) 𝒮.S)
    (Pi : HeckeAlgebra (R := ℤ_[p]) DE 𝒮E →ₐ[ℤ_[p]] A)
    (hPi : IsGaloisInvariantSatake (F := F) DE 𝒮E Pi) :
    ∃ π : HeckeAlgebra (R := ℤ_[p]) D 𝒮 →ₐ[ℤ_[p]] A,
      IsBaseChangeSatake D DE 𝒮 𝒮E π Pi := by
  sorry

/-- **S4, fiber clause.**  The fiber of cyclic base change over a given `Pi` is a torsor
under the character group of `Gal(E/F)`: two eigensystems over `F` with the same base
change differ by twisting the Satake data by a character of `Gal(E/F)` evaluated at
Frobenius.

Langlands, *Base Change for GL(2)*, Annals of Math. Studies 96 (1980), Ch. 1, Property C
(the fiber statement).  Ledger: D-6, plus class field theory for the Artin map.

The Frobenius assignment `frob` is supplied as explicit data rather than constructed: the
Artin reciprocity map that produces it is owned by the class-field-theory hub (node S7,
repriced M → L by the panel), and this packet may not assume it. -/
theorem exists_character_of_isBaseChangeSatake [IsGalois F E]
    (hEF : (Module.finrank F E).Prime)
    (D : Type*) [DivisionRing D] [Algebra F D] [WithRigidification F D]
    (DE : Type*) [DivisionRing DE] [Algebra E DE] [WithRigidification E DE]
    (𝒮 : U₁Data F ℤ_[p] p) (𝒮E : U₁Data E ℤ_[p] p)
    (frob : HeightOneSpectrum (𝓞 F) → (E ≃ₐ[F] E))
    (π π' : HeckeAlgebra (R := ℤ_[p]) D 𝒮 →ₐ[ℤ_[p]] A)
    (Pi : HeckeAlgebra (R := ℤ_[p]) DE 𝒮E →ₐ[ℤ_[p]] A)
    (h : IsBaseChangeSatake D DE 𝒮 𝒮E π Pi)
    (h' : IsBaseChangeSatake D DE 𝒮 𝒮E π' Pi) :
    ∃ χ : (E ≃ₐ[F] E) →* Aˣ,
      ∀ (v : HeightOneSpectrum (𝓞 F)) (hvS : v ∉ 𝒮.S) (hvQ : v ∉ 𝒮.Q) (a a' : SatakeParam A),
        IsSatakeParamAt D 𝒮 π v hvS hvQ a →
        IsSatakeParamAt D 𝒮 π' v hvS hvQ a' →
        a' = ⟨(χ (frob v) : A) * a.first, (χ (frob v) : A) * a.second⟩ := by
  sorry

end CyclicBaseChange

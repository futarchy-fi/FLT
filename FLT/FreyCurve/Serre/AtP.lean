/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.FreyCurve.Serre.LocalInertia
public import FLT.FreyCurve.Serre.LocalTorsion
public import FLT.FreyCurve.Serre.MultiplicativeQuotient
public import FLT.FreyCurve.Serre.ReducibleFiltration
public import FLT.FreyCurve.Serre.Semistable

/-!
# Comparing characters with an unramified local quotient

An inertia-invariant nonzero functional on a representation with two rank-one
constituents forces one of those same constituents to be inertia invariant.
The multiplicative case is derived from Tate uniformization, uniform quadratic-twist
descent, and comparison with local geometric torsion. The remaining good-reduction
input is stated for arbitrary elliptic curves over `ℚ_p` with a stable line; the
Frey local quotient and character leaf are proved conditional on that input.
-/

@[expose] public section

namespace LinearMap

variable {k V G : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- If a representation filtered by two characters has a nonzero functional fixed
by a set of operators, one of its two characters is fixed by the entire set.
No splitting of the filtration is required. -/
theorem one_character_trivial_of_invariant_functional
    (ρ : G → Module.End k V) (χ₁ χ₂ : G → Module.End k k)
    (i : k →ₗ[k] V) (q : V →ₗ[k] k)
    (hexact : LinearMap.range i = LinearMap.ker q)
    (hi : ∀ g x, ρ g (i x) = i (χ₁ g x))
    (hq : ∀ g v, q (ρ g v) = χ₂ g (q v))
    (S : Set G) (r : V →ₗ[k] k) (hr : r ≠ 0)
    (hinv : ∀ g ∈ S, ∀ v, r (ρ g v) = r v) :
    (∀ g ∈ S, ∀ x, χ₁ g x = x) ∨ (∀ g ∈ S, ∀ x, χ₂ g x = x) := by
  classical
  have scalar (f : k →ₗ[k] k) (x : k) : f x = x * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul x 1
  by_cases hri : r (i 1) = 0
  · right
    have hker : ∀ v, q v = 0 → r v = 0 := by
      intro v hv
      obtain ⟨x, rfl⟩ := hexact.symm ▸ (show v ∈ LinearMap.ker q from hv)
      have hx : i x = x • i 1 := by
        simpa only [smul_eq_mul, mul_one] using i.map_smul x 1
      rw [hx, map_smul, hri, smul_zero]
    obtain ⟨v, hv⟩ : ∃ v, r v ≠ 0 := by
      by_contra! h
      exact hr (LinearMap.ext h)
    intro g hg x
    have hz : q (ρ g v - (χ₂ g 1) • v) = 0 := by
      rw [map_sub, hq, map_smul, scalar (χ₂ g), smul_eq_mul, mul_comm]
      exact sub_self _
    have heq := hker _ hz
    rw [map_sub, map_smul, hinv g hg, smul_eq_mul, sub_eq_zero] at heq
    have hone : χ₂ g 1 = 1 := (mul_right_cancel₀ hv (heq.symm.trans (one_mul _).symm))
    rw [scalar (χ₂ g), hone, mul_one]
  · left
    intro g hg x
    have heq : (χ₁ g x) * r (i 1) = x * r (i 1) := by
      calc
        _ = (r.comp i) (χ₁ g x) := (scalar (r.comp i) _).symm
        _ = (r.comp i) x :=
          (congrArg r (hi g x)).symm.trans (hinv g hg (i x))
        _ = _ := scalar (r.comp i) x
    exact mul_right_cancel₀ hri heq

end LinearMap

namespace GaloisRep

variable {K k V : Type*} [Field K] [NumberField K]
  [Field k] [TopologicalSpace k] [AddCommGroup V] [Module k V]

/-- A nonzero inertia-invariant functional on a local representation makes one
of the characters in a global exact filtration unramified at that place.
For the Serre at-p argument, the functional must still be constructed from
the ordinary or multiplicative local theory, with the supersingular case excluded. -/
theorem one_character_unramifiedAt_of_invariant_functional
    (ρ : GaloisRep K k V) (χ₁ χ₂ : GaloisRep K k k)
    (i : k →ₗ[k] V) (q : V →ₗ[k] k)
    (hexact : LinearMap.range i = LinearMap.ker q)
    (hi : ∀ g x, ρ g (i x) = i (χ₁ g x))
    (hq : ∀ g x, q (ρ g x) = χ₂ g (q x))
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : V →ₗ[k] k) (hr : r ≠ 0)
    (hinv : ∀ g ∈ localInertiaGroup v, ∀ x, r (ρ.toLocal v g x) = r x) :
    χ₁.IsUnramifiedAt v ∨ χ₂.IsUnramifiedAt v := by
  have h := LinearMap.one_character_trivial_of_invariant_functional
    (ρ.toLocal v) (χ₁.toLocal v) (χ₂.toLocal v) i q hexact
    (fun g x ↦ hi (Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) g) x)
    (fun g x ↦ hq (Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) g) x)
    (localInertiaGroup v : Set _) r hr hinv
  rcases h with h | h
  · exact Or.inl ⟨fun g hg ↦ LinearMap.ext (h g hg)⟩
  · exact Or.inr ⟨fun g hg ↦ LinearMap.ext (h g hg)⟩

end GaloisRep

open NumberField WeierstrassCurve ValuativeRel
open scoped WeierstrassCurve.Affine

attribute [local instance] completionValuativeRel completion_isNonarchimedeanLocalField
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

/-- Classical equality on local geometric point coordinates. -/
noncomputable local instance localDecidableEq (α : Type*) : DecidableEq α :=
  Classical.typeDecidableEq α

namespace WeierstrassCurve

set_option backward.isDefEq.respectTransparency false in
/-- At multiplicative reduction over a number-field completion, geometric torsion
has a nonzero functional fixed by local inertia. No prime-to-residue assumption is needed. -/
theorem exists_local_invariant_functional_of_multiplicative
    {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (E : WeierstrassCurve (v.adicCompletion F)) [E.IsElliptic]
    (p : ℕ) [Fact p.Prime]
    (hmult : E.HasMultiplicativeReduction 𝒪[v.adicCompletion F]) :
    ∃ r : (E.map (algebraMap (v.adicCompletion F)
        (AlgebraicClosure (v.adicCompletion F)))).nTorsion p →ₗ[ZMod p] ZMod p,
      r ≠ 0 ∧ ∀ σ ∈ localInertiaGroup v, ∀ x,
        r (E.galoisRep p (Fact.out : p.Prime).pos σ x) = r x := by
  classical
  let K := v.adicCompletion F
  let Ω := AlgebraicClosure K
  let : ValuativeRel K := completionValuativeRel v
  let : IsNonarchimedeanLocalField K := completion_isNonarchimedeanLocalField v
  let := hmult
  let A := localClosureValuation v
  have hA : (A.comap (algebraMap K Ω)).toSubring = (algebraMap 𝒪[K] K).range := by
    rw [localClosureValuation_comap]
    have h : algebraMap (v.adicCompletionIntegers F) K =
        (v.adicCompletionIntegers F).subtype := by
      ext x
      rfl
    rw [h]
    change (v.adicCompletionIntegers F).toSubring.subtype.range = _
    rw [Subring.range_subtype, Subring.algebraMap_def, Subring.range_subtype]
    exact (completion_integerRing_eq v).symm
  obtain ⟨r, hr, hinv⟩ := E.exists_inertia_invariant_torsion_quotient A hA p
  let r' : (E.map (algebraMap K Ω)).nTorsion p →+ ZMod p := r
  refine ⟨r'.toZModLinearMap p, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hr 1
    intro hz
    exact zero_ne_one ((LinearMap.congr_fun hz x).symm.trans hx)
  · intro σ hσ x
    exact hinv (localClosureDecomposition v σ)
      (localClosureDecomposition_mem_inertia v σ hσ) x _ rfl

set_option backward.isDefEq.respectTransparency false in
/-- A local invariant functional pulls back to the restricted global torsion representation.
Nonvanishing follows from the general geometric torsion-cardinality theorem. -/
theorem exists_invariant_functional_toLocal
    {F : Type*} [Field F] [NumberField F] [DecidableEq F]
    [DecidableEq (AlgebraicClosure F)]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (p : ℕ) [Fact p.Prime] (hp : 0 < p)
    (hlocal : ∃ r : ((E.map (algebraMap F (v.adicCompletion F))).map
        (algebraMap (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)))).nTorsion p
        →ₗ[ZMod p] ZMod p,
      r ≠ 0 ∧ ∀ σ ∈ localInertiaGroup v, ∀ x,
        r ((E.map (algebraMap F (v.adicCompletion F))).galoisRep p hp σ x) = r x) :
    ∃ r : (E.map (algebraMap F (AlgebraicClosure F))).nTorsion p →ₗ[ZMod p] ZMod p,
      r ≠ 0 ∧ ∀ σ ∈ localInertiaGroup v, ∀ x,
        r ((E.galoisRep p hp).toLocal v σ x) = r x := by
  classical
  obtain ⟨r, hr, hinv⟩ := hlocal
  let f := E.geometricTorsionBaseChange (L := v.adicCompletion F) p
  refine ⟨r.comp f, ?_, ?_⟩
  · intro hz
    apply hr
    ext x
    obtain ⟨y, rfl⟩ := (E.geometricTorsionBaseChange_bijective (L := v.adicCompletion F) hp).2 x
    exact LinearMap.congr_fun hz y
  · intro σ hσ x
    have heq : (E.galoisRep p hp).toLocal v =
        (E.galoisRep p hp).map (algebraMap F (v.adicCompletion F)) := by
      unfold GaloisRep.toLocal
      congr 1
    change r (f ((E.galoisRep p hp).toLocal v σ x)) = r (f x)
    rw [heq, E.geometricTorsionBaseChange_equivariant p hp σ x]
    exact hinv σ hσ _

end WeierstrassCurve

namespace WeierstrassCurve

/-- The remaining general local input at `p`: for a good-reduction elliptic curve
over `ℚ_p`, a Galois-stable `𝔽_p`-line implies a nonzero inertia-invariant functional.
For `p ≥ 5`, this follows from the ordinary connected–étale quotient and exclusion
of supersingular reduction by its irreducible inertia action. It is a proposition,
not an asserted theorem or a Frey-specific assumption. -/
def GoodReductionAtPQuotient (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  let v := hp.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  ∀ (E : WeierstrassCurve K) (_ : E.IsElliptic), E.HasGoodReduction 𝒪[K] →
    (∃ i : ZMod p →ₗ[ZMod p] (E.map (algebraMap K (AlgebraicClosure K))).nTorsion p,
      Function.Injective i ∧ ∀ σ : Field.absoluteGaloisGroup K,
        ∃ a : ZMod p, E.galoisRep p hp.pos σ (i 1) = i a) →
    ∃ r : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion p →ₗ[ZMod p] ZMod p,
      r ≠ 0 ∧ ∀ σ ∈ localInertiaGroup v, ∀ x, r (E.galoisRep p hp.pos σ x) = r x

end WeierstrassCurve

namespace FreyPackage

/-- The local quotient required by the at-`p` Serre leaf, on the actual global torsion module. -/
def HasAtPLocalQuotient (P : FreyPackage) : Prop :=
  letI : Fact P.p.Prime := ⟨P.pp⟩
  Nonempty (GaloisRep.CharacterFiltration (P.freyCurve.galoisRep P.p P.hppos)) →
    ∃ r : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p
        →ₗ[ZMod P.p] ZMod P.p,
      r ≠ 0 ∧ ∀ σ ∈ localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat, ∀ x,
        r ((P.freyCurve.galoisRep P.p P.hppos).toLocal
          P.pp.toHeightOneSpectrumRingOfIntegersRat σ x) = r x

/-- The Frey local quotient exists in both multiplicative cases at `p`, without
any good-reduction input or condition on a character filtration. -/
theorem hasAtPLocalQuotient_of_multiplicative (P : FreyPackage)
    (hmult : HasMultiplicativeReduction
      𝒪[P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ]
      (P.freyCurve.map
        (algebraMap ℚ (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)))) :
    P.HasAtPLocalQuotient := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  intro _
  apply P.freyCurve.exists_invariant_functional_toLocal
    P.pp.toHeightOneSpectrumRingOfIntegersRat P.p P.hppos
  exact WeierstrassCurve.exists_local_invariant_functional_of_multiplicative
    P.pp.toHeightOneSpectrumRingOfIntegersRat _ P.p hmult

set_option backward.isDefEq.respectTransparency false in
/-- Semistability and the general good-reduction input imply the Frey local quotient at `p`.
The multiplicative branches, including nonsplit descent, are fully derived from Tate theory. -/
theorem hasAtPLocalQuotient_of_goodReduction (P : FreyPackage)
    (hgood : WeierstrassCurve.GoodReductionAtPQuotient P.p P.pp) :
    P.HasAtPLocalQuotient := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  intro ⟨F⟩
  let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  obtain hg | hm := P.good_or_multiplicative 𝒪[K] K
  · apply P.freyCurve.exists_invariant_functional_toLocal v P.p P.hppos
    apply hgood (P.freyCurve.map (algebraMap ℚ K)) inferInstance hg
    let f := P.freyCurve.geometricTorsionBaseChange (L := K) P.p
    refine ⟨f.comp F.i,
      (P.freyCurve.geometricTorsionBaseChange_injective P.p).comp F.i_injective, ?_⟩
    intro σ
    let g := Field.absoluteGaloisGroup.map (algebraMap ℚ K) σ
    refine ⟨F.χ₁ g 1, ?_⟩
    change (P.freyCurve.map (algebraMap ℚ K)).galoisRep P.p P.hppos σ (f (F.i 1)) =
      f (F.i (F.χ₁ g 1))
    rw [← P.freyCurve.geometricTorsionBaseChange_equivariant P.p P.hppos σ (F.i 1)]
    exact congrArg f (F.i_equivariant g 1)
  · exact P.hasAtPLocalQuotient_of_multiplicative hm ⟨F⟩

/-- A local quotient makes one of the same two global filtration characters unramified at `p`. -/
theorem one_character_unramified_at_p_of_localQuotient (P : FreyPackage)
    (hlocal : P.HasAtPLocalQuotient) :
    letI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ F : GaloisRep.CharacterFiltration (P.freyCurve.galoisRep P.p P.hppos),
      F.χ₁.IsUnramifiedAt P.pp.toHeightOneSpectrumRingOfIntegersRat ∨
        F.χ₂.IsUnramifiedAt P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  intro F
  obtain ⟨r, hr, hinv⟩ := hlocal ⟨F⟩
  exact GaloisRep.one_character_unramifiedAt_of_invariant_functional
    (P.freyCurve.galoisRep P.p P.hppos) F.χ₁ F.χ₂ F.i F.q F.exactness
    F.i_equivariant F.q_equivariant P.pp.toHeightOneSpectrumRingOfIntegersRat r hr hinv

/-- The at-`p` Serre character leaf conditional only on the general good-reduction
stable-line input. It inherits the existing Tate and torsion-cardinality admissions. -/
theorem one_character_unramified_at_p_of_goodReduction (P : FreyPackage)
    (hgood : WeierstrassCurve.GoodReductionAtPQuotient P.p P.pp) :
    letI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ F : GaloisRep.CharacterFiltration (P.freyCurve.galoisRep P.p P.hppos),
      F.χ₁.IsUnramifiedAt P.pp.toHeightOneSpectrumRingOfIntegersRat ∨
        F.χ₂.IsUnramifiedAt P.pp.toHeightOneSpectrumRingOfIntegersRat :=
  P.one_character_unramified_at_p_of_localQuotient
    (P.hasAtPLocalQuotient_of_goodReduction hgood)

end FreyPackage

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOpenEmbeddings

/-!
# Coherent restrictions to shared occurrence overlaps

Restrictions through nested principal opens agree on the full schemes.
Triple products give compatible paths through different double overlaps
in the same ambient chart, even when the overlap labels are distinct.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  (x : PrincipalOccurrenceStage dst a b f) (hx : ∀ i e, Function.Bijective (x.hom i e))

/-- Each restriction into an occurrence overlap is an actual open immersion. -/
instance principalOccurrenceRestriction_isOpenImmersion (i : ι) (e : J i)
    {r : Stage R (A i) (x.source i)}
    (h : PrimeSpectrum.basicOpen r ≤
      PrimeSpectrum.basicOpen (principalOccurrenceDenominator x i e)) :
    IsOpenImmersion (principalOccurrenceRestriction x hx i e h) := by
  dsimp only [principalOccurrenceRestriction]
  infer_instance

/-- All restriction paths through an intermediate principal open agree. -/
theorem principalOccurrenceRestriction_comp (i : ι) (e : J i)
    {r s : Stage R (A i) (x.source i)}
    (h : PrimeSpectrum.basicOpen r ≤
      PrimeSpectrum.basicOpen (principalOccurrenceDenominator x i e))
    (k : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r) :
    PrincipalLocalizationSquare.openInclusion k ≫ principalOccurrenceRestriction x hx i e h =
      principalOccurrenceRestriction x hx i e (k.trans h) := by
  rw [← cancel_mono (principalOccurrenceOpen x hx i e)]
  simp only [Category.assoc, principalOccurrenceRestriction_fac,
    PrincipalLocalizationSquare.openInclusion_fac]

/-- A map into a shared overlap is determined by its ambient chart map. -/
theorem principalOccurrenceRestriction_unique (i : ι) (e : J i)
    {r : Stage R (A i) (x.source i)}
    (h : PrimeSpectrum.basicOpen r ≤
      PrimeSpectrum.basicOpen (principalOccurrenceDenominator x i e))
    (g : Spec (.of (Localization.Away r)) ⟶
      Spec (.of (PrincipalStage R (B (dst i e)) (b (dst i e)) (x.target (dst i e)))))
    (hg : g ≫ principalOccurrenceOpen x hx i e = PrincipalLocalizationSquare.inclusion r) :
    g = principalOccurrenceRestriction x hx i e h := by
  apply (cancel_mono (principalOccurrenceOpen x hx i e)).mp
  exact hg.trans (principalOccurrenceRestriction_fac x hx i e h).symm

/-- The triple-product open lies in the other double-product open as well. -/
theorem principalOccurrenceTriple_le (i : ι) (e d c : J i) :
    PrimeSpectrum.basicOpen ((principalOccurrenceDenominator x i e *
      principalOccurrenceDenominator x i d) * principalOccurrenceDenominator x i c) ≤
    PrimeSpectrum.basicOpen (principalOccurrenceDenominator x i e *
      principalOccurrenceDenominator x i c) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_left

/-- Two double-overlap paths from the actual triple open have the same restriction. -/
theorem principalOccurrenceRestriction_triangle (i : ι) (e d c : J i) :
    PrincipalLocalizationSquare.openInclusion (PrimeSpectrum.basicOpen_mul_le_left
      (principalOccurrenceDenominator x i e * principalOccurrenceDenominator x i d)
      (principalOccurrenceDenominator x i c)) ≫
        principalOccurrenceRestriction x hx i e (PrimeSpectrum.basicOpen_mul_le_left
          (principalOccurrenceDenominator x i e) (principalOccurrenceDenominator x i d)) =
    PrincipalLocalizationSquare.openInclusion (principalOccurrenceTriple_le x i e d c) ≫
      principalOccurrenceRestriction x hx i e (PrimeSpectrum.basicOpen_mul_le_left
        (principalOccurrenceDenominator x i e) (principalOccurrenceDenominator x i c)) := by
  rw [principalOccurrenceRestriction_comp, principalOccurrenceRestriction_comp]

end FLT.Mazur.FiniteTypeRelationModel

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceAmbientSquares

/-!
# Recovery of occurrence embeddings in the original atlas

The original coordinate equivalences give open embeddings into the original
ambient charts. Their squares with every bijective finite stage are cartesian.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

/-- The original overlap embedding in the incident ambient chart. -/
def principalOccurrenceOriginalOpen (i : ι) (k : J i) :
    Spec (.of (Localization.Away (b (dst i k)))) ⟶ Spec (.of (A i)) :=
  (Scheme.Spec.mapIso ((e i k).toRingEquiv.toCommRingCatIso.op)).hom ≫
    PrincipalLocalizationSquare.inclusion (a i k)

/-- Original coordinate equivalences give open immersions. -/
instance principalOccurrenceOriginalOpen_isOpenImmersion (i : ι) (k : J i) :
    IsOpenImmersion (principalOccurrenceOriginalOpen e i k) := by
  dsimp only [principalOccurrenceOriginalOpen]
  infer_instance

/-- The original occurrence has the prescribed principal image. -/
theorem principalOccurrenceOriginalOpen_opensRange (i : ι) (k : J i) :
    (principalOccurrenceOriginalOpen e i k).opensRange = PrimeSpectrum.basicOpen (a i k) := by
  dsimp only [principalOccurrenceOriginalOpen]
  rw [Scheme.Hom.opensRange_comp_of_isIso, PrincipalLocalizationSquare.inclusion_opensRange]

/-- Explicit coordinates for the original embedding. -/
theorem principalOccurrenceOriginalOpen_eq_spec (i : ι) (k : J i) :
    principalOccurrenceOriginalOpen e i k = Spec.map (CommRingCat.ofHom
      (((e i k).toAlgHom).comp
        (IsScalarTower.toAlgHom R (A i) (Localization.Away (a i k)))).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (e i k).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (A i) (Localization.Away (a i k)))) = _
  rw [← Spec.map_comp]
  rfl

variable [∀ i, Algebra.FiniteType R (A i)] [∀ j, Algebra.FiniteType R (B j)]

variable (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))

/-- Projection from an original ambient chart to its finite relation model. -/
abbrev principalOccurrenceAmbientProjection (i : ι) :
    Spec (.of (A i)) ⟶ Spec (.of (Stage R (A i) (x.source i))) :=
  Spec.map (CommRingCat.ofHom (stageMap R (A i) (x.source i)).toRingHom)

/-- Projection from an original overlap to its literal shared finite target. -/
abbrev principalOccurrenceOverlapProjection (j : κ) :
    Spec (.of (Localization.Away (b j))) ⟶
      Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) :=
  Spec.map (CommRingCat.ofHom (principalStageMap R (B j) (b j) (x.target j)).toRingHom)

/-- The entire original occurrence square commutes. -/
@[reassoc (attr := simp)] theorem principalOccurrenceOriginalOpen_fac (i : ι) (k : J i) :
    principalOccurrenceOverlapProjection e x (dst i k) ≫ principalOccurrenceOpen x hx i k =
      principalOccurrenceOriginalOpen e i k ≫ principalOccurrenceAmbientProjection e x i := by
  rw [principalOccurrenceOpen_eq_spec, principalOccurrenceOriginalOpen_eq_spec]
  simp only [principalOccurrenceOverlapProjection, principalOccurrenceAmbientProjection,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (principalOccurrenceAmbientHom_fac x i k)

/-- The original occurrence square is a genuine base change. -/
theorem principalOccurrenceOriginalOpen_isPullback (i : ι) (k : J i) :
    IsPullback (principalOccurrenceOverlapProjection e x (dst i k))
      (principalOccurrenceOriginalOpen e i k) (principalOccurrenceOpen x hx i k)
      (principalOccurrenceAmbientProjection e x i) := by
  apply IsOpenImmersion.isPullback
  · exact (principalOccurrenceOriginalOpen_fac e x hx i k).symm
  · rw [principalOccurrenceOpen_opensRange, principalOccurrenceOriginalOpen_opensRange]
    rw [show principalOccurrenceAmbientProjection e x i ⁻¹ᵁ
        PrimeSpectrum.basicOpen (principalOccurrenceDenominator x i k) =
        PrimeSpectrum.basicOpen (stageMap R (A i) (x.source i)
          (principalOccurrenceDenominator x i k)) from PrimeSpectrum.comap_basicOpen _ _]
    congr 1
    exact (stageMap_mk R (A i) (x.source i) _).trans
      (principalRepresentative_spec R (A i) (a i k))

end FLT.Mazur.FiniteTypeRelationModel

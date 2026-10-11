/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedDegreeProjMap
public import FLT.Mazur.GradedProjRegradedEvaluation

/-!
# Original unit-coordinate evaluations under global regrading

The glued Proj comparison commutes with actual evaluation of homogeneous
coordinates on every scheme where the chosen denominator is invertible.
-/

@[expose] public noncomputable section
open HomogeneousLocalization AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.GradedDegreeProjUnitNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (f : A →+* B) (r : ℕ) (hf : ∀ d a, a ∈ 𝒜 d → f a ∈ ℬ (r * d))

/-- The scaled fraction construction agrees with the general regraded fraction construction. -/
theorem awayMap_eq_regraded (s : A) :
    GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf s =
      HomogeneousLocalizationRegradedMap.map 𝒜 ℬ f (r * ·) hf
        (by rintro _ ⟨k, rfl⟩; exact ⟨k, (map_pow f s k).symm⟩) := by
  apply RingHom.ext
  intro z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rfl

/-- Applying the actual fraction map before evaluation gives the original composite evaluation. -/
theorem evaluation_comp {X : Scheme.{u}} (φ : B →+* Γ(X, ⊤))
    (s : A) (hu : IsUnit (φ (f s))) :
    (GradedProjUnitChart.evaluation ℬ φ (f s) hu).comp
        (GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf s) =
      GradedProjUnitChart.evaluation 𝒜 (φ.comp f) s hu := by
  rw [awayMap_eq_regraded]
  exact GradedProjRegradedEvaluation.evaluation_comp 𝒜 ℬ f (r * ·) hf φ s hu _

/-- The global comparison retains every actual invertible-coordinate evaluation map. -/
@[reassoc]
theorem toProj_map (hr : 0 < r)
    (hcover : (⨆ i : Σ d : PNat, 𝒜 d, Proj.basicOpen ℬ (f i.2)) = ⊤)
    {X : Scheme.{u}} (φ : B →+* Γ(X, ⊤)) {d : ℕ}
    (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (φ (f s))) :
    GradedProjUnitChart.toProj ℬ φ (f s) hu (hf d s hs) (Nat.mul_pos hr hd) ≫
        GradedDegreeProjMap.map 𝒜 ℬ f r hf hr hcover =
      GradedProjUnitChart.toProj 𝒜 (φ.comp f) s hu hs hd := by
  rw [GradedProjUnitChart.toProj, Category.assoc,
    GradedDegreeProjMap.awayι_map 𝒜 ℬ f r hf hr hcover s hs hd,
    GradedDegreeProjOverlap.chartMap]
  unfold GradedProjUnitChart.toProj GradedProjUnitChart.toAffine
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, evaluation_comp]

end FLT.Mazur.GradedDegreeProjUnitNaturality

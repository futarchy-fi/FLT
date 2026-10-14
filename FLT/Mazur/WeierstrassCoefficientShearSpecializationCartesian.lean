/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Cartesian specialization of the complete coefficient model

The actual specialization square is a pullback, so faithful coefficients
cover the original model and detect its finite presentation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (r : S) (v : T) (j : ℕ) (hj : j ≤ n) (f : S →ₐ[R] T)
local notation "gS" => coefficientShearGluedStructure hπ data S r j hj
local notation "gT" => coefficientShearGluedStructure hπ data T v j hj
local notation "p" => coefficientShearSpecialization hπ data S T r v j hj f
local notation "b" => Spec.map (CommRingCat.ofHom f.toRingHom)

/-- Specialization retains the full original coefficient fiber product. -/
theorem coefficientShearSpecialization_isPullback : IsPullback p gT gS b := by
  apply IsPullback.flip
  apply IsPullback.of_bot _
    (coefficientShearSpecialization_structure hπ data S T r v j hj f).symm
    (coefficientShearGlued_isPullback hπ data S r j hj)
  rw [coefficientShearSpecialization_projection]
  have hb : b ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext f.commutes)
  rw [hb]
  exact coefficientShearGlued_isPullback hπ data T v j hj

/-- Faithful coefficient specialization gives a flat surjection on the full model. -/
theorem coefficientShearSpecialization_flat_surjective (hf : f.toRingHom.FaithfullyFlat) :
    Flat p ∧ Surjective p := by
  obtain ⟨hb, hb'⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom f.toRingHom)).mpr hf
  have H := (coefficientShearSpecialization_isPullback hπ data S T r v j hj f).flip
  exact ⟨MorphismProperty.of_isPullback H hb, MorphismProperty.of_isPullback H hb'⟩

/-- Finite presentation descends from the complete equation model over faithful coefficients. -/
theorem coefficientShearSpecialization_lfp (hf : f.toRingHom.FaithfullyFlat)
    [LocallyOfFinitePresentation gT] : LocallyOfFinitePresentation gS := by
  obtain ⟨hb, hb'⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom f.toRingHom)).mpr hf
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (coefficientShearSpecialization_isPullback hπ data S T r v j hj f).flip
    ⟨⟨hb', hb⟩, inferInstance⟩ inferInstance

end FLT.Mazur.WeierstrassDividedDepth

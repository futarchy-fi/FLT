/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatHomogeneousLocalizationBaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Cartesian affine charts for flat Proj base change

The homogeneous-localization equivalence identifies each standard affine
chart after flat scalar extension with the base change of the original chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open scoped TensorProduct FLT.Mazur.HomogeneousLocalizationScalars
universe u
namespace FLT.Mazur.FlatGradedProjChartBaseChange
open GradedProjBaseChangeMap HomogeneousLocalizationBaseChange FlatHomogeneousLocalizationBaseChange
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  [Module.Flat R B] {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

include hf in
/-- The degree-zero localization square is a pushout of commutative rings. -/
lemma isPushout_away :
    IsPushout (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (GradedProjStructuralMap.scalarToAway 𝒜 f))
      (CommRingCat.ofHom (GradedProjStructuralMap.scalarToAway
        (baseGrade (B := B) 𝒜) (inclusion 𝒜 f)))
      (CommRingCat.ofHom (Away.map (inclusion (B := B) 𝒜) f)) := by
  refine (CommRingCat.isPushout_tensorProduct R B (Away 𝒜 f)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (equiv (B := B) 𝒜 f hf).toRingEquiv.toCommRingCatIso
    (by simp) (by ext r; rfl) ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change comparison (B := B) 𝒜 f (b ⊗ₜ[R] 1) = algebraMap B _ b
    rw [comparison_tmul, map_one, Algebra.algebraMap_eq_smul_one]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change comparison (B := B) 𝒜 f (1 ⊗ₜ[R] x) = Away.map (inclusion 𝒜) f x
    rw [comparison_tmul, one_smul]

include hf in
/-- Each standard affine chart of Proj forms a Cartesian square under flat base change. -/
lemma isPullback_away :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map (inclusion (B := B) 𝒜) f)))
      (Spec.map (CommRingCat.ofHom (GradedProjStructuralMap.scalarToAway
        (baseGrade (B := B) 𝒜) (inclusion 𝒜 f))))
      (Spec.map (CommRingCat.ofHom (GradedProjStructuralMap.scalarToAway 𝒜 f)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_away (B := B) 𝒜 hf).flip

end FLT.Mazur.FlatGradedProjChartBaseChange

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionProjectiveGluing
public import FLT.Mazur.ProjectiveProductChartCover
public import FLT.Mazur.ProjectiveTwistAffineBaseChange

/-!
# The section morphism over its coefficient scheme

The chart scalar formulas imply the global morphism commutes with the given
structural map to Spec R, by the actual generator open cover.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (M : X.Modules) {R : Type u} [CommRing R] (n : ℕ)
    (t : Fin (n + 1) → Γ(M, ⊤))
/-- The chart map respects its given scalar coefficient homomorphism. -/
lemma sectionProjectiveChartMorphism_baseProjection (i : Fin (n + 1)) (U : X.Opens)
    (hi : U ≤ sectionGeneratorOpen M (t i)) (r : R →+* Γ(X, U)) :
    sectionProjectiveChartMorphism M n t i U hi r ≫ baseProjection R (Fin (n + 1)) =
      U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom r) := by
  rw [sectionProjectiveChartMorphism, Category.assoc, Category.assoc,
    chartMap_baseProjection, ← Spec.map_comp]
  change U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((U.topIso.inv.hom.comp (sectionProjectiveChartRingMap M n t i U hi r)).comp
      (chartScalars R (Fin (n + 1)) i))) = _
  have he : (sectionProjectiveChartRingMap M n t i U hi r).comp
      (chartScalars R (Fin (n + 1)) i) = r :=
    RingHom.ext (sectionProjectiveChartRingMap_scalar M n t i U hi r)
  rw [RingHom.comp_assoc, he]
  change U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom r ≫ U.topIso.inv) = _
  rw [Spec.map_comp]
  rfl
/-- The glued projective morphism commutes with the actual structural map. -/
lemma sectionProjectiveMorphism_baseProjection
    (ht : ⨆ i, sectionGeneratorOpen M (t i) = ⊤) (q : X ⟶ Spec (.of R)) :
    sectionProjectiveMorphism M n t ht
      (q.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) ≫
        baseProjection R (Fin (n + 1)) = q := by
  apply (sectionGeneratorCover M n t ht).hom_ext
  intro i
  change (sectionGeneratorOpen M (t i)).ι ≫ _ = _
  rw [sectionGeneratorOpen_ι_projectiveMorphism_assoc]
  rw [sectionProjectiveLocalMorphism, sectionProjectiveChartMorphism_baseProjection]
  exact openCoefficientRingMap_square q (sectionGeneratorOpen M (t i))
end FLT.Mazur.FCurve

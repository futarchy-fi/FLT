/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionProjectiveGluing
public import FLT.Mazur.ProjectiveChartSectionPullback
public import FLT.Mazur.ProjectiveTwistChartSection
public import FLT.Mazur.ModuleUnitCocyclePullback

/-!
# Pullback of the hyperplane transition along the section morphism

The actual structure-sheaf pullback agrees with the section ratio on every
common source subopen, including its restriction transports and orientation.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (M : X.Modules) {R : Type} [CommRing R] (n : ℕ)
    (t : Fin (n + 1) → Γ(M, ⊤))
    (ht : ⨆ i, sectionGeneratorOpen M (t i) = ⊤) (r : R →+* Γ(X, ⊤))
/-- The glued map has the ratio-chart formula on every generator subopen. -/
lemma sectionProjectiveMorphism_onOpen (i : Fin (n + 1)) (U : X.Opens)
    (hi : U ≤ sectionGeneratorOpen M (t i)) :
    U.ι ≫ sectionProjectiveMorphism M n t ht r =
      sectionProjectiveChartMorphism M n t i U hi (sectionChartScalars r U) := by
  rw [← X.homOfLE_ι hi, Category.assoc, sectionGeneratorOpen_ι_projectiveMorphism]
  simp only [sectionProjectiveLocalMorphism, sectionProjectiveChartMorphism_restrict,
    sectionChartScalars_restrict]
attribute [local irreducible] sectionProjectiveMorphism

/-- The glued map pulls each chart coordinate to the actual section ratio. -/
lemma sectionProjectiveMorphism_chartSection (i j : Fin (n + 1)) (U : X.Opens)
    (hi : U ≤ sectionProjectiveMorphism M n t ht r ⁻¹ᵁ chart R (Fin (n + 1)) i) :
    (sectionProjectiveMorphism M n t ht r).appLE (chart R (Fin (n + 1)) i) U hi
      (Proj.awayToSection (grading R (Fin (n + 1))) (MvPolynomial.X i)
        (coordinate R (Fin (n + 1)) i j)) =
      sectionRatioOn M (t i) U ((sectionProjectiveMorphism_preimage_chart M n t ht r i) ▸ hi)
        (t j) := by
  have hi' : U ≤ sectionGeneratorOpen M (t i) :=
    (sectionProjectiveMorphism_preimage_chart M n t ht r i) ▸ hi
  calc
    _ = sectionProjectiveChartRingMap M n t i U hi' (sectionChartScalars r U)
        (coordinate R (Fin (n + 1)) i j) :=
      chartSection_evaluation_apply R (Fin (n + 1)) i U
        (sectionProjectiveChartRingMap M n t i U hi' (sectionChartScalars r U))
        (sectionProjectiveMorphism M n t ht r) hi
        (sectionProjectiveMorphism_onOpen M n t ht r i U hi') _
    _ = _ := sectionProjectiveChartRingMap_coordinate M n t i U hi'
      (sectionChartScalars r U) j
/-- The actual pulled-back hyperplane transition equals the section ratio. -/
lemma sectionProjectiveMorphism_transition (i j : Fin (n + 1)) (U : X.Opens)
    (hi : U ≤ sectionProjectiveMorphism M n t ht r ⁻¹ᵁ chart R (Fin (n + 1)) i)
    (hj : U ≤ sectionProjectiveMorphism M n t ht r ⁻¹ᵁ chart R (Fin (n + 1)) j) :
    ((twistCocycle R (Fin (n + 1)) 1).inverseImageUnit
      (sectionProjectiveMorphism M n t ht r) i j U hi hj : Γ(X, U)) =
      sectionRatioOn M (t i) U ((sectionProjectiveMorphism_preimage_chart M n t ht r i) ▸ hi)
        (t j) := by
  change (sectionProjectiveMorphism M n t ht r).appLE _ _ _
    ((twistCocycle R (Fin (n + 1)) 1).unit i j
      (chart R (Fin (n + 1)) i ⊓ chart R (Fin (n + 1)) j) inf_le_left inf_le_right :
        Γ(space R (Fin (n + 1)), chart R (Fin (n + 1)) i ⊓ chart R (Fin (n + 1)) j)) = _
  rw [twistCocycle_one_chartSection]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  exact sectionProjectiveMorphism_chartSection M n t ht r i j U hi
end FLT.Mazur.FCurve

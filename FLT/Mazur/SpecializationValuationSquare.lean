/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!+# Actual valuation squares witnessing specializations

For an original source point whose image specializes to a target point,
construct a valuation ring inside the source residue field. The generic
map is exactly the original residue-field map, and the closed point maps
exactly to the prescribed target point. No lift to the source is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.SpecializationValuationSquare
universe u
set_option backward.isDefEq.respectTransparency.types false
variable {Y X : Scheme.{u}} (π : Y ⟶ X)

/-- An actual original specialization produces a square with its exact residue-field map. -/
theorem exists_square (e : Y) (x : X) (h : π e ⤳ x) :
    ∃ D : ValuativeCommSq π,
      D.i₁ (default : Spec (.of D.K)) = e ∧ D.i₂ (closedPoint D.R) = x := by
  let φ : X.presheaf.stalk x ⟶ Y.residueField e :=
    X.presheaf.stalkSpecializes h ≫ π.stalkMap e ≫ Y.residue e
  obtain ⟨A, hA, hlocal⟩ := exists_factor_valuationRing φ.hom
  let ψ : X.presheaf.stalk x ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (φ.hom.codRestrict _ hA)
  have hw : Y.fromSpecResidueField e ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap A (Y.residueField e))) ≫
        Spec.map ψ ≫ X.fromSpecStalk x := by
    rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  let D : ValuativeCommSq π :=
    { R := A, K := Y.residueField e, commSq := ⟨hw⟩, .. }
  refine ⟨D, Y.fromSpecResidueField_apply e _, ?_⟩
  change (Spec.map ψ ≫ X.fromSpecStalk x) (closedPoint A) = x
  rw [Scheme.Hom.comp_apply]
  have hc : Spec.map ψ (closedPoint A) = closedPoint (X.presheaf.stalk x) :=
    comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
  rw [hc, X.fromSpecStalk_closedPoint]

/-- Every such valuation square retains the original specialization in the target. -/
theorem specializes (D : ValuativeCommSq π) :
    π (D.i₁ (default : Spec (.of D.K))) ⤳ D.i₂ (closedPoint D.R) := by
  have hw := congrArg (fun g : Spec (.of D.K) ⟶ X ↦ g default) D.commSq.w
  simp only [Scheme.Hom.comp_apply] at hw
  rw [hw]
  exact (specializes_closedPoint _).map D.i₂.continuous

end FLT.Mazur.SpecializationValuationSquare

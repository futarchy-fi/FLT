/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Valuation rings realizing an actual image specialization

An image specialization has a valuative square whose generic point is the
specified source point and whose closed point is the specified target point.
The fraction field is the source residue field. No lift to the source is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.SchemeSpecializationValuation
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct a valuation square with both its generic and closed images prescribed. -/
theorem exists_square (x : X) (y : Y) (h : f x ⤳ y) :
    ∃ S : ValuativeCommSq f, S.i₁ default = x ∧ S.i₂ (closedPoint S.R) = y := by
  let g : Y.presheaf.stalk y ⟶ X.residueField x :=
    Y.presheaf.stalkSpecializes h ≫ f.stalkMap x ≫ X.residue x
  obtain ⟨A, hA, hlocal⟩ := exists_factor_valuationRing g.hom
  let a : Y.presheaf.stalk y ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (g.hom.codRestrict _ hA)
  have hw : X.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x))) ≫
        Spec.map a ≫ Y.fromSpecStalk y := by
    rw [Scheme.fromSpecResidueField, Category.assoc,
      ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨{ R := A, K := X.residueField x, commSq := ⟨hw⟩, .. },
    X.fromSpecResidueField_apply x default, ?_⟩
  change (Spec.map a ≫ Y.fromSpecStalk y) (closedPoint A) = y
  rw [Scheme.Hom.comp_apply]
  have ha : Spec.map a (closedPoint A) = closedPoint (Y.presheaf.stalk y) :=
    comap_closedPoint (S := A) (g.hom.codRestrict A.toSubring hA)
  rw [ha, Y.fromSpecStalk_closedPoint]

/-- Any lift of such a square specializes its generic source point to a point above the center. -/
theorem lift_specializes (S : ValuativeCommSq f) (l : S.commSq.LiftStruct) :
    S.i₁ default ⤳ l.l (closedPoint S.R) ∧
      f (l.l (closedPoint S.R)) = S.i₂ (closedPoint S.R) := by
  constructor
  · have he := congrArg (fun t : Spec (.of S.K) ⟶ X ↦ t default) l.fac_left
    rw [← he]
    exact (specializes_closedPoint _).map l.l.continuous
  · exact congrArg (fun t : Spec (.of S.R) ⟶ Y ↦ t (closedPoint S.R)) l.fac_right

end FLT.Mazur.SchemeSpecializationValuation

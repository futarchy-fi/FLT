/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveCoordinates
public import FLT.Mazur.WeierstrassCoefficientShearTangentRootEvaluation

/-!
# Actual integral tangent comparison in strict split polygon coordinates

Evaluate the genuine integral tangent model at its two split residue roots.
The whole evaluated comparison is the intrinsic polygon reflection when the
source uses the original orientation and the target the opposite orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => coefficientShearRootStrictPositiveCoordinates
  hπ data D s hs hstart hk hp
local notation "O" => coefficientShearRootStrictPositiveOppositeCoordinates
  hπ data D s hs hstart hk hp
local notation "ρ" => coefficientShearRootStrictPositivePolygonReflectionIso
  hπ data D s hs hstart hk hp

include D in
omit [IsDomain R] [IsBezout R] in
/-- The original split root is an actual root of the original integral tangent equation. -/
theorem coefficientShearSplitRoot_zero :
    (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 - algebraMap R K W.a₂ = 0 := by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem

include D in
omit [IsDomain R] [IsBezout R] in
/-- The other split residue root is the actual companion in the original tangent cover. -/
theorem coefficientShearSplitRoot_companion :
    (-algebraMap R K W.a₁) ^ 2 + algebraMap R K W.a₁ * (-algebraMap R K W.a₁) -
      algebraMap R K W.a₂ = 0 := by
  simpa only [sub_zero] using
    nodeTangentCompanion_equation W K 0 (coefficientShearSplitRoot_zero D)

/-- Root change preserves the whole first-orientation polygon coordinates. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCoordinates_rootChange (r t : K) :
    (C r).hom ≫ (coefficientShearRootChange hπ data K r t (s + 1) hs).hom =
      (C t).hom := by
  simp only [coefficientShearRootStrictPositiveCoordinates, coefficientShearRootChange,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- Changing from first to opposite coordinates gives the intrinsic full polygon reflection. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCoordinates_rootChange_reflection (r t : K) :
    (C r).hom ≫ (coefficientShearRootChange hπ data K r t (s + 1) hs).hom =
      (ρ).hom ≫ (O t).hom := by
  rw [← coefficientShearRootStrictPositiveCoordinates_reflection,
    ← Category.assoc, coefficientShearRootStrictPositivePolygonReflection_involutive,
    Category.id_comp, coefficientShearRootStrictPositiveCoordinates_rootChange]

local notation "t" => -algebraMap R K W.a₁
local notation "M₀" => coefficientShearTangentRootSpecialization
  hπ data K 0 (coefficientShearSplitRoot_zero D) (s + 1) hs
local notation "Mt" => coefficientShearTangentRootSpecialization
  hπ data K t (coefficientShearSplitRoot_companion D) (s + 1) hs
local notation "σ" => coefficientShearTangentConjugation hπ data (s + 1) hs

/-- The actual integral tangent conjugation has the proved complete polygon reflection formula. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCoordinates_tangentConjugation :
    (C 0).hom ≫ M₀ ≫ σ = (ρ).hom ≫ (O t).hom ≫ Mt := by
  rw [coefficientShearTangentRootSpecialization_conjugation
    hπ data K 0 (coefficientShearSplitRoot_zero D) (s + 1) hs t
    (coefficientShearSplitRoot_companion D) (zero_add t),
    ← Category.assoc, coefficientShearRootStrictPositiveCoordinates_rootChange_reflection,
    Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth

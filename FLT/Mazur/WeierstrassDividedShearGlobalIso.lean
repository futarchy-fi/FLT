/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearGlobalCover

/-!
# Shear of the entire original finite global modification

The actual infinity lift and finite local shear glue across their full
original intersection to an isomorphism over the original cubic shear.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (r : R)
  (j : ℕ) (hj : j ≤ n)
local notation "dat" => fun a => shearData (data a) r
local notation "U" => rootShearCurve W r
local notation "C" => WeierstrassCurve.VariableChange.mk (1 : Rˣ) 0 r 0
local notation "i" => integralVariableChangeIso W U C rfl
local notation "m" => shearFiniteModificationIso hπ data r j hj
local notation "f" => finiteGlobalContraction hπ dat j hj ≫ Iso.hom i

local notation "l" => shearFiniteInfinityLift hπ data r j hj
local notation "q" => Iso.inv m ≫ finiteLocalChart hπ dat j hj


/-- The entire original finite global model is identified with its integral shear. -/
def shearFiniteGlobalIso : finiteGlobalModel hπ dat j hj ≅ finiteGlobalModel hπ data j hj :=
  (SchemeOpenPushout.coverIso (affineBoundaryToY W) (finiteYBoundary hπ data j hj)
    (l) (q) (shearFiniteGlobal_overlap_isPullback hπ data r j hj)
    (shearFiniteGlobal_charts_cover hπ data r j hj)).symm

/-- The inverse comparison on the original infinity chart is its actual translated lift. -/
@[reassoc] theorem shearFiniteGlobalIso_inv_infinity :
    finiteInfinityChart hπ data j hj ≫ (shearFiniteGlobalIso hπ data r j hj).inv = (l) :=
  SchemeOpenPushout.inl_coverIso _ _ _ _
    (shearFiniteGlobal_overlap_isPullback hπ data r j hj)
    (shearFiniteGlobal_charts_cover hπ data r j hj)

/-- The inverse comparison restricts to the inverse of the complete finite local shear. -/
@[reassoc] theorem shearFiniteGlobalIso_inv_local :
    finiteLocalChart hπ data j hj ≫ (shearFiniteGlobalIso hπ data r j hj).inv = (q) :=
  SchemeOpenPushout.inr_coverIso _ _ _ _
    (shearFiniteGlobal_overlap_isPullback hπ data r j hj)
    (shearFiniteGlobal_charts_cover hπ data r j hj)

/-- The global comparison restricts to the entire original finite local comparison. -/
@[reassoc] theorem shearFiniteGlobalIso_local :
    finiteLocalChart hπ dat j hj ≫ (shearFiniteGlobalIso hπ data r j hj).hom =
      (m).hom ≫ finiteLocalChart hπ data j hj := by
  apply (cancel_mono (shearFiniteGlobalIso hπ data r j hj).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc,
    shearFiniteGlobalIso_inv_local, Iso.hom_inv_id_assoc]

/-- The whole inverse comparison retains the exact original cubic contraction. -/
@[reassoc] theorem shearFiniteGlobalIso_inv_contraction :
    (shearFiniteGlobalIso hπ data r j hj).inv ≫ (f) =
      finiteGlobalContraction hπ data j hj := by
  apply pushout.hom_ext
  · change finiteInfinityChart hπ data j hj ≫ _ = finiteInfinityChart hπ data j hj ≫ _
    rw [shearFiniteGlobalIso_inv_infinity_assoc, shearFiniteInfinityLift_contraction,
      finiteInfinityChart_contraction]
  · change finiteLocalChart hπ data j hj ≫ _ = finiteLocalChart hπ data j hj ≫ _
    rw [shearFiniteGlobalIso_inv_local_assoc, shearFiniteLocalInv_contraction,
      finiteLocalChart_contraction]

/-- The entire original global shear square commutes over the actual integral cubic isomorphism. -/
@[reassoc] theorem shearFiniteGlobalIso_contraction :
    (shearFiniteGlobalIso hπ data r j hj).hom ≫ finiteGlobalContraction hπ data j hj =
      finiteGlobalContraction hπ dat j hj ≫ (i).hom := by
  rw [← shearFiniteGlobalIso_inv_contraction hπ data r j hj, Iso.hom_inv_id_assoc]

/-- The whole global comparison square is cartesian, including infinity and exceptional charts. -/
theorem shearFiniteGlobalIso_isPullback :
    IsPullback (shearFiniteGlobalIso hπ data r j hj).hom
      (finiteGlobalContraction hπ dat j hj) (finiteGlobalContraction hπ data j hj) (i).hom :=
  IsPullback.of_horiz_isIso ⟨shearFiniteGlobalIso_contraction hπ data r j hj⟩

/-- The global shear preserves the original coefficient structure morphism. -/
@[reassoc] theorem shearFiniteGlobalIso_structure :
    (shearFiniteGlobalIso hπ data r j hj).hom ≫ finiteGlobalStructure hπ data j hj =
      finiteGlobalStructure hπ dat j hj := by
  rw [finiteGlobalStructure, shearFiniteGlobalIso_contraction_assoc]
  change _ ≫ integralVariableChangeTo W U C rfl ≫ integralCurveStructure W = _
  rw [integralVariableChangeTo_structure]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

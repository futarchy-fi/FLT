/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearGlobalInfinityOpen

/-!
# Lifting the original infinity chart into the sheared finite global model

Use the entire unchanged infinity preimage to construct its actual lift.
The local finite shear agrees with this lift on the original overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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

/-- The sheared contraction viewed over the original cubic is unchanged at original infinity. -/
theorem finiteGlobal_shearToOriginalY_isIso :
    IsIso ((f) ∣_ (integralCurveChart W 1).opensRange) :=
  SchemeUnchangedOpen.isIso_comp _ _ _
    (finiteGlobal_shearOriginalY_isIso hπ data r j hj) inferInstance

/-- The actual original infinity chart lifted into the full sheared global modification. -/
def shearFiniteInfinityLift : chartScheme W 1 ⟶ finiteGlobalModel hπ dat j hj :=
  SchemeUnchangedOpen.lift (f) (integralCurveChart W 1)
    (finiteGlobal_shearToOriginalY_isIso hπ data r j hj)

instance shearFiniteInfinityLift_isOpenImmersion :
    IsOpenImmersion (shearFiniteInfinityLift hπ data r j hj) := by
  unfold shearFiniteInfinityLift
  infer_instance

/-- The infinity lift retains its original cubic inclusion after the actual shear. -/
@[reassoc] theorem shearFiniteInfinityLift_contraction :
    shearFiniteInfinityLift hπ data r j hj ≫ (f) = integralCurveChart W 1 :=
  SchemeUnchangedOpen.lift_comp _ _ _

/-- The lift is the complete infinity pullback, including every point above the chart. -/
theorem shearFiniteInfinityLift_isPullback :
    IsPullback (𝟙 _) (shearFiniteInfinityLift hπ data r j hj) (integralCurveChart W 1) (f) :=
  SchemeUnchangedOpen.lift_isPullback _ _ _

/-- The inverse local shear contracts to the exact original affine-to-projective map. -/
@[reassoc] theorem shearFiniteLocalInv_contraction :
    (m).inv ≫ finiteLocalChart hπ dat j hj ≫ (f) = finiteToCurve hπ data j hj := by
  rw [finiteLocalChart_contraction_assoc, ← shearFiniteModificationIso_toCurve,
    Iso.inv_hom_id_assoc]

/-- The local shear and the infinity lift agree on the actual original gluing boundary. -/
theorem shearFiniteInfinityLift_overlap :
    affineBoundaryToY W ≫ shearFiniteInfinityLift hπ data r j hj =
      finiteYBoundary hπ data j hj ≫ (m).inv ≫ finiteLocalChart hπ dat j hj := by
  let H := shearFiniteInfinityLift_isPullback hπ data r j hj
  have hw : affineBoundaryToY W ≫ integralCurveChart W 1 =
      (finiteYBoundary hπ data j hj ≫ (m).inv ≫ finiteLocalChart hπ dat j hj) ≫ (f) := by
    rw [Category.assoc, Category.assoc, shearFiniteLocalInv_contraction,
      ← finiteToAffine_toCurve, finiteYBoundary_contraction_assoc]
    exact (yz_isPullback W).w
  have ha := H.lift_fst (affineBoundaryToY W)
    (finiteYBoundary hπ data j hj ≫ (m).inv ≫ finiteLocalChart hπ dat j hj) hw
  have hb := H.lift_snd (affineBoundaryToY W)
    (finiteYBoundary hπ data j hj ≫ (m).inv ≫ finiteLocalChart hπ dat j hj) hw
  simpa only [Category.comp_id] using ha ▸ hb

end FLT.Mazur.WeierstrassDividedDepth

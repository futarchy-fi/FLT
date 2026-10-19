/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationNegation
public import FLT.Mazur.WeierstrassDividedGlobalInitialAction

/-!
# The original inverse on the whole initial finite global model

Transport the constructed projective inverse through the exact initial-model
comparison. Its involution, original contraction and integral base are retained.
This is the base case for extending inverse through the later divided stages.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => finiteGlobalInitialIso hπ data
local notation "M" => finiteGlobalModel hπ data 0 (Nat.zero_le n)
local notation "c" => finiteGlobalContraction hπ data 0 (Nat.zero_le n)
local notation "N" => WeierstrassGlobalModification.globalNegationIso W (π ^ start)
  (d).b3 (d).b4 (d).b6 (d).factor3 (d).factor4 (d).factor6 (pow_ne_zero start hπ)

/-- Negation of the entire actual initial finite model, including its exceptional fiber. -/
def finiteGlobalInitialNegationIso : M ≅ M := e ≪≫ N ≪≫ (e).symm

/-- The inverse map is the same actual initial negative. -/
theorem finiteGlobalInitialNegationIso_inv :
    (finiteGlobalInitialNegationIso hπ data).inv =
      (finiteGlobalInitialNegationIso hπ data).hom := by
  simp only [finiteGlobalInitialNegationIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rfl

/-- The initial negative retains precisely the original Weierstrass inverse after contraction. -/
@[reassoc] theorem finiteGlobalInitialNegationIso_contraction :
    (finiteGlobalInitialNegationIso hπ data).hom ≫ c = c ≫ integralCurveNegation W := by
  simp only [finiteGlobalInitialNegationIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    finiteGlobalInitialIso_inv_contraction, WeierstrassGlobalModification.globalNegationIso]
  rw [WeierstrassGlobalModification.globalNegation_contraction,
    finiteGlobalInitialIso_contraction_assoc]

/-- The transported inverse is involutive on the entire initial model. -/
@[reassoc] theorem finiteGlobalInitialNegationIso_comp :
    (finiteGlobalInitialNegationIso hπ data).hom ≫
      (finiteGlobalInitialNegationIso hπ data).hom = 𝟙 M := by
  calc
    _ = (finiteGlobalInitialNegationIso hπ data).hom ≫
        (finiteGlobalInitialNegationIso hπ data).inv :=
      congrArg ((finiteGlobalInitialNegationIso hπ data).hom ≫ ·)
        (finiteGlobalInitialNegationIso_inv hπ data).symm
    _ = _ := (finiteGlobalInitialNegationIso hπ data).hom_inv_id

/-- The exact original integral coefficient map is fixed by initial negation. -/
@[reassoc] theorem finiteGlobalInitialNegationIso_structure :
    (finiteGlobalInitialNegationIso hπ data).hom ≫
        finiteGlobalStructure hπ data 0 (Nat.zero_le n) =
      finiteGlobalStructure hπ data 0 (Nat.zero_le n) := by
  rw [finiteGlobalStructure, finiteGlobalInitialNegationIso_contraction_assoc,
    integralCurveNegation_structure]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSmoothTerminalIntegralAction
public import FLT.Mazur.WeierstrassDividedTensorPointAction
public import FLT.Mazur.WeierstrassSmoothDividedResiduePoint
public import FLT.Mazur.WeierstrassSmoothDividedTerminalTensorAction

/-!
# The actual coefficient action on the terminal divided tensor input

The proved integral action specializes along the concrete secant residue map.
Both pullback projections identify the result with the coefficient action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (D : SplitNodeDepth W π depth) (hk0 : 0 < start + j)
  (hk : 2 * (start + j) ≤ depth) (hp : 2 * (start + j) = depth)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "e" => smoothDividedSecantResidue D d hk0 hk hp
local notation "f" => AlgHom.comp e (smoothDividedSecantInput d)
local notation "g" => AlgHom.comp e (smoothDividedIntegralOutput d
  (IsRegular.of_ne_zero (pow_ne_zero _ hπ)))
local notation "c" => finiteDividedGlobalChart hπ data j hj
local notation "a" => smoothHorizontalResiduePoint D (by omega)
local notation "ha" => smoothHorizontalResiduePoint_structure D (by omega)
local notation "aR" => a ≫ originalSmoothCoefficientMap K W
local notation "point" => dividedGlobalTensorAlgebraPoint hπ data j hj K C

/-- The specialized terminal output is the actual finite integral point action. -/
theorem smoothTerminalResidue_finitePointAction :
    finiteGlobalPointAction hπ data j hj aR
      (Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ c)
      (finiteDividedGlobalChart_algebra_condition hπ data j hj aR f (by
        rw [Category.assoc, originalSmoothCoefficientMap_structure, ← Category.assoc, ha]
        exact specAlgHom_structure (IsScalarTower.toAlgHom R K C))) =
      Spec.map (CommRingCat.ofHom (g).toRingHom) ≫ c := by
  have h := smoothTerminalIntegral_finitePointAction_specialize hπ data j hj
    (Spec.map (CommRingCat.ofHom (e).toRingHom))
  simp only [smoothDividedSecantResidue_point D d hk0 hk hp] at h
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using h

/-- The genuine terminal residue output carries the coefficient-model point action. -/
theorem smoothTerminalResidue_coefficientPointAction :
    finiteGlobalCoefficientPointAction hπ data j hj K a (point f)
      (dividedGlobalTensorAlgebraPoint_condition hπ data j hj K C a ha f) =
        point g :=
  dividedGlobalTensorAlgebraPoint_action hπ data j hj K C a ha f g
    (smoothTerminalResidue_finitePointAction hπ data j hj D hk0 hk hp)

/-- The scalar-extended integral input is exactly the original terminal tensor input. -/
theorem smoothTerminalResidue_tensorInput :
    point f = Spec.map (CommRingCat.ofHom
      (smoothDividedTerminalTensorInput D d hk0 hk hp).toRingHom) ≫
        globalDividedTensorChart hπ data K j hj := rfl

/-- The scalar-extended genuine output is exactly the original terminal tensor output. -/
theorem smoothTerminalResidue_tensorOutput :
    point g = Spec.map (CommRingCat.ofHom
      (smoothDividedTerminalTensorOutput D d hk0 hk hp).toRingHom) ≫
        globalDividedTensorChart hπ data K j hj := rfl

end FLT.Mazur.WeierstrassDividedDepth

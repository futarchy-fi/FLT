/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSmoothSuccessiveIntegralAction
public import FLT.Mazur.WeierstrassSmoothSuccessiveIntegralResiduePoint
public import FLT.Mazur.WeierstrassSmoothSuccessiveResidueOutputs

/-!
# Both original residue actions in the actual finite model

The integral equality specializes along the two proved original residue
factorizations. The resulting point actions retain the original smooth
parameter and the independently constructed successive input and output maps.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
  (D : SplitNodeDepth W π depth) (hk : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => olderGlobalChart hπ data j hj r hr
local notation "a" => smoothHorizontalResiduePoint D (by omega) ≫
  originalSmoothCoefficientMap K W
local notation "ha" => smoothSuccessiveResiduePoint_structure D (by omega)

/-- The first specialized original output is the actual finite-model point action. -/
theorem smoothSuccessiveFirstResidue_finitePointAction :
    finiteGlobalPointAction hπ data (j + 1 + r) hr a
      (Spec.map (CommRingCat.ofHom
        (smoothSuccessiveFirstResidueInput e hπ D (Nat.zero_lt_succ _) hk).toRingHom) ≫ c)
      (olderGlobalChart_algebra_condition hπ data j hj r hr a
        (smoothSuccessiveFirstResidueInput e hπ D (Nat.zero_lt_succ _) hk) ha) =
      Spec.map (CommRingCat.ofHom
        (smoothSuccessiveFirstResidueOutput e hπ D (Nat.zero_lt_succ _) hk).toRingHom) ≫ c := by
  have h := smoothSuccessiveIntegral_finitePointAction_specialize hπ data j hj r hr
    (Spec.map (CommRingCat.ofHom
      (smoothSuccessiveFirstIntegralResidue e hπ D (Nat.zero_lt_succ _) hk).toRingHom))
  simp only [smoothSuccessiveFirstIntegralResidue_point e hπ D hk] at h
  simpa only [smoothSuccessiveFirstResidueInput, smoothSuccessiveFirstResidueOutput,
    AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
    Spec.map_comp, Category.assoc] using h

/-- The second specialized original output is the actual finite-model point action. -/
theorem smoothSuccessiveSecondResidue_finitePointAction :
    finiteGlobalPointAction hπ data (j + 1 + r) hr a
      (Spec.map (CommRingCat.ofHom
        (smoothSuccessiveSecondResidueInput e hπ D (Nat.zero_lt_succ _) hk).toRingHom) ≫ c)
      (olderGlobalChart_algebra_condition hπ data j hj r hr a
        (smoothSuccessiveSecondResidueInput e hπ D (Nat.zero_lt_succ _) hk) ha) =
      Spec.map (CommRingCat.ofHom
        (smoothSuccessiveSecondResidueOutput e hπ D (Nat.zero_lt_succ _) hk).toRingHom) ≫ c := by
  have h := smoothSuccessiveIntegral_finitePointAction_specialize hπ data j hj r hr
    (Spec.map (CommRingCat.ofHom
      (smoothSuccessiveSecondIntegralResidue e hπ D (Nat.zero_lt_succ _) hk).toRingHom))
  simp only [smoothSuccessiveSecondIntegralResidue_point e hπ D hk] at h
  simpa only [smoothSuccessiveSecondResidueInput, smoothSuccessiveSecondResidueOutput,
    AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
    Spec.map_comp, Category.assoc] using h

end FLT.Mazur.WeierstrassDividedDepth

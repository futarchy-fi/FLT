/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderTensorPointAction
public import FLT.Mazur.WeierstrassDividedSmoothSuccessiveResidueAction
public import FLT.Mazur.WeierstrassSmoothSuccessiveTransportedTensorInput

/-!
# The actual coefficient action on both original interior inputs

Both projections identify the scalar-extended integral outputs with the
actual coefficient action. The input points are the independent original
tensor maps already identified with the labeled cyclic punctures.
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
  (D : SplitNodeDepth W π depth) (hk0 : 0 < start + j)
  (hk : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => olderGlobalTensorChart hπ data K j hj r hr
local notation "a" => smoothHorizontalResiduePoint D (lt_of_le_of_lt (Nat.zero_le _) hk)
local notation "ha" => smoothHorizontalResiduePoint_structure D (lt_of_le_of_lt (Nat.zero_le _) hk)
local notation "point" => olderGlobalTensorAlgebraPoint hπ data j hj r hr K C

/-- The first integral residue input extends to the independent original tensor point. -/
theorem smoothSuccessiveFirstResidue_tensorPoint :
    point (smoothSuccessiveFirstResidueInput e hπ D (Nat.zero_lt_succ _) hk) =
      Spec.map (CommRingCat.ofHom (smoothSuccessiveFirstTensorInput D e hk0 hk).toRingHom) ≫
        c := by
  change Spec.map (CommRingCat.ofHom
    (smoothSuccessiveFirstTransportedTensorInput e hπ D hk).toRingHom) ≫ c = _
  rw [smoothSuccessiveFirstTransportedTensorInput_eq e hπ D hk0 hk]

omit hk0 in
/-- The first genuine residue output carries the actual coefficient-model action. -/
theorem smoothSuccessiveFirstResidue_coefficientPointAction :
    finiteGlobalCoefficientPointAction hπ data (j + 1 + r) hr K a
      (point (smoothSuccessiveFirstResidueInput e hπ D (Nat.zero_lt_succ _) hk))
      (olderGlobalTensorAlgebraPoint_condition hπ data j hj r hr K C a ha
        (smoothSuccessiveFirstResidueInput e hπ D (Nat.zero_lt_succ _) hk)) =
      point (smoothSuccessiveFirstResidueOutput e hπ D (Nat.zero_lt_succ _) hk) :=
  olderGlobalTensorAlgebraPoint_action hπ data j hj r hr K C a ha _ _
    (smoothSuccessiveFirstResidue_finitePointAction hπ data j hj r hr D hk)

/-- The second integral residue input extends to the independent original tensor point. -/
theorem smoothSuccessiveSecondResidue_tensorPoint :
    point (smoothSuccessiveSecondResidueInput e hπ D (Nat.zero_lt_succ _) hk) =
      Spec.map (CommRingCat.ofHom (smoothSuccessiveSecondTensorInput D e hk0 hk).toRingHom) ≫
        c := by
  change Spec.map (CommRingCat.ofHom
    (smoothSuccessiveSecondTransportedTensorInput e hπ D hk).toRingHom) ≫ c = _
  rw [smoothSuccessiveSecondTransportedTensorInput_eq e hπ D hk0 hk]

omit hk0 in
/-- The second genuine residue output carries the actual coefficient-model action. -/
theorem smoothSuccessiveSecondResidue_coefficientPointAction :
    finiteGlobalCoefficientPointAction hπ data (j + 1 + r) hr K a
      (point (smoothSuccessiveSecondResidueInput e hπ D (Nat.zero_lt_succ _) hk))
      (olderGlobalTensorAlgebraPoint_condition hπ data j hj r hr K C a ha
        (smoothSuccessiveSecondResidueInput e hπ D (Nat.zero_lt_succ _) hk)) =
      point (smoothSuccessiveSecondResidueOutput e hπ D (Nat.zero_lt_succ _) hk) :=
  olderGlobalTensorAlgebraPoint_action hπ data j hj r hr K C a ha _ _
    (smoothSuccessiveSecondResidue_finitePointAction hπ data j hj r hr D hk)

end FLT.Mazur.WeierstrassDividedDepth

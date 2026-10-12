/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbit
public import FLT.Mazur.WeierstrassDividedSmoothSuccessiveCoefficientAction
public import FLT.Mazur.WeierstrassSmoothSuccessiveTensorOutput

/-!
# The actual sheared action on original successive tensor inputs

The inputs come from the integral incidence transport and the outputs from
its genuine action. This includes the first retained chart at scale one:
only the next depth is required to be positive.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n)
  (D : SplitNodeDepth W π depth) (hk : 2 * (start + j + 1) < depth)
  (r : ResidueField R)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => smoothHorizontalResiduePoint D D.depth_pos
local notation "ha" => smoothHorizontalResiduePoint_structure D D.depth_pos
local notation "V" => W.map (algebraMap R K)
local notation "B" => coefficientShearRetainedTensorChart hπ data K r
  (j + 1 + m) hm (Fin.mk j (by omega))
local notation "E" => coefficientShearGluedIso hπ data K r (j + 1 + m) hm
local notation "g" => coefficientShearGluedStructure hπ data K r (j + 1 + m) hm
local notation "i₁" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (smoothSuccessiveFirstTransportedTensorInput e hπ D hk))) ≫ B
local notation "i₂" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (smoothSuccessiveSecondTransportedTensorInput e hπ D hk))) ≫ B
local notation "o₁" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (smoothSuccessiveFirstTensorOutput e hπ D hk))) ≫ B
local notation "o₂" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (smoothSuccessiveSecondTensorOutput e hπ D hk))) ≫ B

/-- The first transported tensor input has the actual smooth point's coefficient map. -/
theorem coefficientShearSuccessiveFirst_condition :
    a ≫ integralSmoothStructure V = i₁ ≫ g := by
  simp only [coefficientShearGluedStructure, Category.assoc,
    coefficientShearRetainedTensorChart_original_assoc hπ data K r j hj m hm]
  exact olderGlobalTensorAlgebraPoint_condition hπ data j hj m hm K C a ha
    (smoothSuccessiveFirstResidueInput e hπ D (Nat.zero_lt_succ _) hk)

/-- The opposite transported tensor input has the same actual coefficient map. -/
theorem coefficientShearSuccessiveSecond_condition :
    a ≫ integralSmoothStructure V = i₂ ≫ g := by
  simp only [coefficientShearGluedStructure, Category.assoc,
    coefficientShearRetainedTensorChart_original_assoc hπ data K r j hj m hm]
  exact olderGlobalTensorAlgebraPoint_condition hπ data j hj m hm K C a ha
    (smoothSuccessiveSecondResidueInput e hπ D (Nat.zero_lt_succ _) hk)

/-- The first independent integral tensor output is the complete sheared smooth action. -/
theorem coefficientShearSuccessiveFirst_action :
    pullback.lift a i₁
        (coefficientShearSuccessiveFirst_condition hπ data j hj m hm D hk r) ≫
      coefficientShearAction hπ data K r (j + 1 + m) hm = o₁ := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearAction_pair]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    coefficientShearRetainedTensorChart_original hπ data K r j hj m hm]
  exact smoothSuccessiveFirstResidue_coefficientPointAction hπ data j hj m hm D hk

/-- The second independent integral tensor output is the complete sheared smooth action. -/
theorem coefficientShearSuccessiveSecond_action :
    pullback.lift a i₂
        (coefficientShearSuccessiveSecond_condition hπ data j hj m hm D hk r) ≫
      coefficientShearAction hπ data K r (j + 1 + m) hm = o₂ := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearAction_pair]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    coefficientShearRetainedTensorChart_original hπ data K r j hj m hm]
  exact smoothSuccessiveSecondResidue_coefficientPointAction hπ data j hj m hm D hk

end FLT.Mazur.WeierstrassDividedDepth

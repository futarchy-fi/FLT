/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoBranches

/-!
# Arbitrary-target uniqueness on both length-two attachment opens

The full-node scheme pushouts detect maps from each actual attachment.
The two conic restrictions come from the same complete terminal component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 1 (by omega))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "tangent" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "G₁" => olderGlobalZeroFirstNode hπ data D 0 hs 0 hs
  hstart hk
local notation "G₂" => olderGlobalZeroSecondNode hπ data D 0 hs 0 hs
  hstart hk
local notation "Z" => zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp
local notation "ρ" => Iso.inv (ProjectiveLine.endpointReversalIso K)

variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (0 + 1) hs ⟶ Y)
  (h : ∀ i, (zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp i).left ≫ f =
    (zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp i).left ≫ g)

include h in
/-- Component agreement determines the entire first original attachment open. -/
theorem zeroEqualityCycleComponent_lengthTwo_first_hom_ext :
    G₁ ≫ f = G₁ ≫ g := by
  apply (fullNodeBranches_isPushout a c ha).hom_ext
  · apply (cancel_epi (fullNodeConicParameterIso a c ha).hom).mp
    have H := congrArg (fun q =>
      equalityTerminalFirstNodeParameter data D 0 hs hk hp ≫ ρ ≫ q) (h 1)
    simp only [zeroEqualityCycleComponent_lengthTwo_first_conic_assoc] at H
    simpa only [Category.assoc] using H
  · have H := congrArg (fun q =>
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso tangent).hom ≫ q) (h 0)
    simp only [zeroEqualityCycleComponent_lengthTwo_first_exterior_assoc] at H
    simpa only [Category.assoc] using H

include h in
/-- Component agreement determines the entire second original attachment open. -/
theorem zeroEqualityCycleComponent_lengthTwo_second_hom_ext :
    G₂ ≫ f = G₂ ≫ g := by
  apply (fullNodeBranches_isPushout (-a) c (ha).neg).hom_ext
  · apply (cancel_epi (fullNodeConicParameterIso (-a) c (ha).neg).hom).mp
    have H := congrArg (fun q =>
      equalityTerminalSecondNodeParameter data D 0 hs hk hp ≫ ρ ≫ q) (h 1)
    simp only [zeroEqualityCycleComponent_lengthTwo_second_conic_assoc] at H
    simpa only [Category.assoc] using H
  · have H := congrArg (fun q =>
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
        Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso tangent).hom ≫ q) (h 0)
    simp only [zeroEqualityCycleComponent_lengthTwo_second_exterior_assoc] at H
    simpa only [Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth

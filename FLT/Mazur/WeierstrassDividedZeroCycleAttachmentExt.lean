/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleAttachmentBranches

/-!
# Cyclic component maps detect morphisms on the actual start-zero attachments

The scheme pushout on each original localized node upgrades agreement on
the adjacent cyclic components to equality on the entire node open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 1 (by omega))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : 0 + 1 + s ≤ n) hs (by omega))
local notation "G₁" => olderGlobalZeroFirstNode hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "G₂" => olderGlobalZeroSecondNode hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Agreement on the actual cyclic components determines the whole first attachment open. -/
theorem zeroSplitCycleComponent_first_attachment_hom_ext :
    G₁ ≫ transport ≫ f = G₁ ≫ transport ≫ g := by
  apply (fullNodeBranches_isPushout a c ha).hom_ext
  · apply (cancel_epi (fullNodeConicParameterIso a c ha).hom).mp
    apply (cancel_epi (E).hom).mp
    have H := congrArg (fun q => ProjectiveLine.right K ≫ q) (h 1)
    simp only [zeroSplitCycleComponent_first_attachment_conic_assoc] at H
    simpa only [Category.assoc] using H
  · have H := congrArg (fun q =>
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫
        ProjectiveLine.left K ≫
        (ProjectiveLine.slopeNormalizationIso (Units.mk0 a (IsUnit.ne_zero ha))).hom ≫ q) (h 0)
    simp only [zeroSplitCycleComponent_first_attachment_exterior_assoc] at H
    simpa only [Category.assoc] using H

include h in
/-- Agreement likewise determines the whole opposite attachment, with its translated branch. -/
theorem zeroSplitCycleComponent_second_attachment_hom_ext :
    G₂ ≫ transport ≫ f = G₂ ≫ transport ≫ g := by
  apply (fullNodeBranches_isPushout (-a) c (ha).neg).hom_ext
  · apply (cancel_epi (fullNodeConicParameterIso (-a) c (ha).neg).hom).mp
    apply (cancel_epi (E).hom).mp
    have H := congrArg (fun q => ProjectiveLine.left K ≫ q) (h ⟨2 * s + 2, by omega⟩)
    simp only [zeroSplitCycleComponent_second_attachment_conic_assoc] at H
    simpa only [Category.assoc] using H
  · have H := congrArg (fun q =>
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
        Spec.map (CommRingCat.ofHom
          (Polynomial.aeval (Polynomial.X - Polynomial.C a)).toRingHom) ≫
        ProjectiveLine.left K ≫
        (ProjectiveLine.slopeNormalizationIso (Units.mk0 a (IsUnit.ne_zero ha))).hom ≫ q) (h 0)
    simp only [zeroSplitCycleComponent_second_attachment_exterior_assoc] at H
    simpa only [Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth

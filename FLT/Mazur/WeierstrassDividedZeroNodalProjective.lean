/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroNodalGluing
public import FLT.Mazur.WeierstrassNodalResidueTransition

/-!
# The entire zero-stage residue model is the split nodal projective cubic

Both complete charts and their full intersection are retained. The comparison
is an isomorphism of schemes and preserves the actual residue structure map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth)
  (j : ℕ) (hj : j ≤ n) (hzero : start + j = 0)
open WeierstrassIntegralChart WeierstrassDilatation
local notation "K" => ResidueField R
local notation "N" => splitNodalEquation (residueTangentUnit D)
local notation "f" => nodalResidueChartIso D hdepth 1
local notation "r" => terminalZeroNodalChart hπ data D hdepth j hj hzero

/-- The full nodal infinity chart with its actual global inclusion. -/
def zeroNodalInfinityChart : chartScheme N 1 ⟶ finiteGlobalTensorModel hπ data K j hj :=
  (f).hom ≫ finiteInfinityTensorChart hπ data K j hj

instance zeroNodalInfinityChart_isOpenImmersion :
    IsOpenImmersion (zeroNodalInfinityChart hπ data D hdepth j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Normalization retains the whole infinity open. -/
theorem zeroNodalInfinityChart_range :
    Set.range (zeroNodalInfinityChart hπ data D hdepth j hj) =
      Set.range (finiteInfinityTensorChart hπ data K j hj) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(f).hom x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (f).hom.homeomorph.surjective x
    exact ⟨y, congrArg (finiteInfinityTensorChart hπ data K j hj) hy⟩

/-- The actual global gluing has exactly the original nodal Y/Z transition. -/
@[reassoc] theorem zeroNodalProjective_overlap :
    affineBoundaryToY N ≫ zeroNodalInfinityChart hπ data D hdepth j hj =
      overlapInclusion N 2 1 ≫ r := by
  rw [zeroNodalInfinityChart, ← Category.assoc, ← nodalResidueBoundaryIso_infinity]
  exact terminalZeroBoundary_overlap hπ data D hdepth j hj hzero

/-- The full nodal overlap is the cartesian intersection of the two normalized charts. -/
theorem zeroNodalProjective_isPullback :
    IsPullback (affineBoundaryToY N) (overlapInclusion N 2 1)
      (zeroNodalInfinityChart hπ data D hdepth j hj) r := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (zeroNodalProjective_overlap hπ data D hdepth j hj hzero).symm
  apply TopologicalSpace.Opens.ext
  change r ⁻¹' Set.range (zeroNodalInfinityChart hπ data D hdepth j hj) = _
  rw [zeroNodalInfinityChart_range]
  exact terminalZeroBoundary_preimage hπ data D hdepth j hj hzero

/-- The complete nodal charts cover the actual zero-stage model. -/
theorem zeroNodalProjective_cover (z : finiteGlobalTensorModel hπ data K j hj) :
    (∃ x, zeroNodalInfinityChart hπ data D hdepth j hj x = z) ∨ ∃ x, r x = z := by
  change z ∈ Set.range (zeroNodalInfinityChart hπ data D hdepth j hj) ∪ Set.range r
  rw [zeroNodalInfinityChart_range]
  exact zeroNodal_charts_cover hπ data D hdepth j hj hzero z

/-- The whole original residue model is the split nodal projective cubic. -/
def zeroNodalProjectiveIso : integralCurve N ≅ finiteGlobalTensorModel hπ data K j hj :=
  (yzPushoutIso N).symm ≪≫ SchemeOpenPushout.coverIso _ _ _ _
    (zeroNodalProjective_isPullback hπ data D hdepth j hj hzero)
    (zeroNodalProjective_cover hπ data D hdepth j hj hzero)

/-- The projective comparison retains the full original infinity chart. -/
@[reassoc] theorem zeroNodalProjectiveIso_infinity :
    integralCurveChart N 1 ≫ (zeroNodalProjectiveIso hπ data D hdepth j hj hzero).hom =
      zeroNodalInfinityChart hπ data D hdepth j hj := by
  rw [← inl_yzPushoutIso N]
  simp only [zeroNodalProjectiveIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, SchemeOpenPushout.inl_coverIso]

/-- The projective comparison retains the exact terminal nodal affine chart. -/
@[reassoc] theorem zeroNodalProjectiveIso_terminal :
    integralCurveChart N 2 ≫ (zeroNodalProjectiveIso hπ data D hdepth j hj hzero).hom = r := by
  rw [← inr_yzPushoutIso N]
  simp only [zeroNodalProjectiveIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, SchemeOpenPushout.inr_coverIso]

end FLT.Mazur.WeierstrassDividedDepth

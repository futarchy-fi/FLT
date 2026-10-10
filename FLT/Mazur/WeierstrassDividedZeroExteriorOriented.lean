/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroExteriorProjective
public import FLT.Mazur.ProjectiveLineSlopeNormalizationCharts

/-!
# The ordered retained start-zero exterior component

Normalize the actual retained start-zero component so its first original node is zero
and its second original node is infinity. The coefficient projection and
both global node sections are retained as scheme morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "u" => Units.mk0 a (IsUnit.ne_zero (D.a₁_unit.map (residue R)))
local notation "E" => zeroRetainedExteriorCurve hπ data D j hj r hr hk0 hk
local notation "e" => zeroRetainedExteriorProjectiveIso hπ data D j hj r hr hk0 hk

/-- The actual initial exterior component with ordered polygon endpoints. -/
def zeroRetainedExteriorOrientedIso : E ≅ ProjectiveLine.scheme K :=
  e ≪≫ ProjectiveLine.slopeNormalizationIso u

/-- The normalization is over the original residue field. -/
@[reassoc] theorem zeroRetainedExteriorOrientedIso_structure :
    (zeroRetainedExteriorOrientedIso hπ data D j hj r hr hk0 hk).hom ≫
      ProjectiveLine.toBase K = zeroRetainedExteriorStructure hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedExteriorOrientedIso, Iso.trans_hom, Category.assoc,
    ProjectiveLine.slopeNormalizationIso_base, zeroRetainedExteriorProjectiveIso_structure]

/-- The entire original affine incidence chart uses the proved projective normalization. -/
@[reassoc] theorem zeroRetainedExteriorOrientedIso_affine :
    zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk ≫
      (zeroRetainedExteriorOrientedIso hπ data D j hj r hr hk0 hk).hom =
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom := by
  rw [zeroRetainedExteriorOrientedIso, Iso.trans_hom,
    zeroRetainedExteriorProjectiveIso_affine_assoc]

/-- The entire original infinity torus has the standard reciprocal left coordinate. -/
@[reassoc] theorem zeroRetainedExteriorOrientedIso_laurent :
    zeroRetainedExteriorLaurentChart hπ data D j hj r hr hk0 hk ≫
      (zeroRetainedExteriorOrientedIso hπ data D j hj r hr hk0 hk).hom =
        ProjectiveLine.overlapRight K ≫ ProjectiveLine.left K := by
  rw [zeroRetainedExteriorOrientedIso, Iso.trans_hom,
    zeroRetainedExteriorProjectiveIso_laurent_assoc,
    ProjectiveLine.slopeNormalization_infinityTorus_left]

/-- The normalized projective component still maps into the original global residue model. -/
def zeroRetainedOrientedToGlobal : ProjectiveLine.scheme K ⟶
    finiteGlobalTensorModel hπ data K (j + 1 + r) hr :=
  (zeroRetainedExteriorOrientedIso hπ data D j hj r hr hk0 hk).inv ≫
    zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk

/-- The normalized map is the original projective component map with its inverse coordinates. -/
theorem zeroRetainedOrientedToGlobal_eq :
    zeroRetainedOrientedToGlobal hπ data D j hj r hr hk0 hk =
      (ProjectiveLine.slopeNormalizationIso u).inv ≫
        zeroRetainedProjectiveToGlobal hπ data D j hj r hr hk0 hk := by
  simp only [zeroRetainedOrientedToGlobal, zeroRetainedExteriorOrientedIso, Iso.trans_inv,
    zeroRetainedProjectiveToGlobal, Category.assoc]

/-- The polygon zero endpoint is the original first retained start-zero node. -/
@[reassoc] theorem zeroRetainedOrientedToGlobal_zero :
    ProjectiveLine.zero K ≫ zeroRetainedOrientedToGlobal hπ data D j hj r hr hk0 hk =
      olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedOrientedToGlobal_eq, ProjectiveLine.slopeNormalization_inv_zero_assoc]
  exact zeroRetainedProjectiveToGlobal_first hπ data D j hj r hr hk0 hk

/-- The polygon infinity endpoint is the original second retained start-zero node. -/
@[reassoc] theorem zeroRetainedOrientedToGlobal_infinity :
    ProjectiveLine.infinity K ≫ zeroRetainedOrientedToGlobal hπ data D j hj r hr hk0 hk =
      olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedOrientedToGlobal_eq, ProjectiveLine.slopeNormalization_inv_infinity_assoc]
  exact zeroRetainedProjectiveToGlobal_second hπ data D j hj r hr hk0 hk

/-- The normalized component retains the actual global coefficient projection. -/
@[reassoc] theorem zeroRetainedOrientedToGlobal_structure :
    zeroRetainedOrientedToGlobal hπ data D j hj r hr hk0 hk ≫
      CategoryTheory.Limits.pullback.fst _ _ = ProjectiveLine.toBase K := by
  rw [zeroRetainedOrientedToGlobal, Category.assoc, ← zeroRetainedExteriorStructure,
    ← zeroRetainedExteriorOrientedIso_structure hπ data D j hj r hr hk0 hk,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth

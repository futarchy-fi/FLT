/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing
public import FLT.Mazur.WeierstrassDividedOlderGlobalComponentSections
public import FLT.Mazur.WeierstrassDividedAdjacentParameterIntersection

/-!
# Complete retained normalization components between adjacent node levels

Each full conic parameter is glued to its matching full line at the next
level. The original signed reciprocal tangent scales are retained at every
later stage. These maps include both affine origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "P₁" => adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr
local notation "P₂" => adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr
local notation "G₁" => olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr (by omega) hkNext
local notation "G₂" => olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr (by omega) hkNext

/-- The full first parameter meets its next line with the original reciprocal scale. -/
theorem adjacentRetainedFirstComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ (E).hom ≫ P₁ =
      Spec.map (CommRingCat.ofHom
        (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹))) ≫
          ProjectiveLine.overlapLeft K ≫ G₁ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  simpa only [Category.assoc] using
    (adjacentRetainedFirstParameter_isPullback hπ data D j hj hk0 hk
      hjNext hkNext r hr).w.symm

/-- The complete first projective component retained in the actual global model. -/
def adjacentRetainedFirstComponent :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (j + 2 + r) hr :=
  ProjectiveLine.scaledReciprocalDesc (tangent)⁻¹ ((E).hom ≫ P₁) G₁
    (adjacentRetainedFirstComponent_overlap hπ data D j hj hk0 hk hjNext hkNext r hr)

/-- The first chart is the entire original first conic parameter. -/
@[reassoc] theorem adjacentRetainedFirstComponent_left :
    ProjectiveLine.left K ≫
      adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      (E).hom ≫ P₁ := ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- The second chart retains the matching full line with its original signed scale. -/
@[reassoc] theorem adjacentRetainedFirstComponent_right :
    ProjectiveLine.right K ≫
      adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ G₁ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

/-- The zero endpoint is the original first conic parameter origin. -/
@[reassoc] theorem adjacentRetainedFirstComponent_zero :
    ProjectiveLine.zero K ≫
      adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicParameterOrigin c))) ≫ P₁ := by
  rw [ProjectiveLine.zero, Category.assoc, adjacentRetainedFirstComponent_left,
    ← Category.assoc, conicZeroAffineIso_origin]

/-- The infinity endpoint is the next original first retained node. -/
@[reassoc] theorem adjacentRetainedFirstComponent_infinity :
    ProjectiveLine.infinity K ≫
        adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      olderGlobalFirstSection hπ data D (j + 1) hjNext r hr (by omega) hkNext := by
  rw [ProjectiveLine.infinity, Category.assoc, adjacentRetainedFirstComponent_right,
    ← Category.assoc, ProjectiveLine.chartZero_chartScaling]
  exact olderGlobalFirstSection_line hπ data D (j + 1) hjNext r hr (by omega) hkNext

/-- The full second parameter meets its next line with the original reciprocal scale. -/
theorem adjacentRetainedSecondComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ (E).hom ≫ P₂ =
      Spec.map (CommRingCat.ofHom
        (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹))) ≫
          ProjectiveLine.overlapLeft K ≫ G₂ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  simpa only [Category.assoc] using
    (adjacentRetainedSecondParameter_isPullback hπ data D j hj hk0 hk
      hjNext hkNext r hr).w.symm

/-- The complete second projective component retained in the actual global model. -/
def adjacentRetainedSecondComponent :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (j + 2 + r) hr :=
  ProjectiveLine.scaledReciprocalDesc (-tangent)⁻¹ ((E).hom ≫ P₂) G₂
    (adjacentRetainedSecondComponent_overlap hπ data D j hj hk0 hk hjNext hkNext r hr)

/-- The first chart is the entire original second conic parameter. -/
@[reassoc] theorem adjacentRetainedSecondComponent_left :
    ProjectiveLine.left K ≫
      adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      (E).hom ≫ P₂ := ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- The second chart retains the matching full line with its original signed scale. -/
@[reassoc] theorem adjacentRetainedSecondComponent_right :
    ProjectiveLine.right K ≫
      adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ G₂ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

/-- The zero endpoint is the original second conic parameter origin. -/
@[reassoc] theorem adjacentRetainedSecondComponent_zero :
    ProjectiveLine.zero K ≫
      adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicParameterOrigin c))) ≫ P₂ := by
  rw [ProjectiveLine.zero, Category.assoc, adjacentRetainedSecondComponent_left,
    ← Category.assoc, conicZeroAffineIso_origin]

/-- The infinity endpoint is the next original second retained node. -/
@[reassoc] theorem adjacentRetainedSecondComponent_infinity :
    ProjectiveLine.infinity K ≫
        adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      olderGlobalSecondSection hπ data D (j + 1) hjNext r hr (by omega) hkNext := by
  rw [ProjectiveLine.infinity, Category.assoc, adjacentRetainedSecondComponent_right,
    ← Category.assoc, ProjectiveLine.chartZero_chartScaling]
  exact olderGlobalSecondSection_line hπ data D (j + 1) hjNext r hr (by omega) hkNext

end FLT.Mazur.WeierstrassDividedDepth

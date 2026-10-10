/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing
public import FLT.Mazur.WeierstrassDividedInitialParameterOverlap

/-!
# Complete initial projective components in every retained global stage

The original initial conic parameters glue to the first retained horizontal
lines with their original reciprocal scales. Both marked endpoints are retained.
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
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
  (r : ℕ) (hr : 1 + r ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 d) (Data.factor6 d))
local notation "E" => conicZeroAffineIso c hc
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "P₁" => initialGlobalConicFirstParameter hπ data D (1 + r) hr hstart (by omega)
local notation "P₂" => initialGlobalConicSecondParameter hπ data D (1 + r) hr hstart (by omega)
local notation "G₁" => olderGlobalMiddleFirstLine hπ data D 0 h1 r hr hstart hk
local notation "G₂" => olderGlobalMiddleSecondLine hπ data D 0 h1 r hr hstart hk

/-- The full first parameter meets its next line with the original reciprocal scale. -/
theorem initialGlobalFirstComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ (E).hom ≫ P₁ =
      Spec.map (CommRingCat.ofHom
        (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹))) ≫
          ProjectiveLine.overlapLeft K ≫ G₁ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  exact initialGlobalFirstParameter_overlap hπ data D h1 hstart hk r hr

/-- The complete first projective component retained in the actual global model. -/
def initialGlobalFirstComponent :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (1 + r) hr :=
  ProjectiveLine.scaledReciprocalDesc (tangent)⁻¹ ((E).hom ≫ P₁) G₁
    (initialGlobalFirstComponent_overlap hπ data D h1 hstart hk r hr)

/-- The first chart is the entire original first conic parameter. -/
@[reassoc] theorem initialGlobalFirstComponent_left :
    ProjectiveLine.left K ≫
      initialGlobalFirstComponent hπ data D h1 hstart hk r hr =
      (E).hom ≫ P₁ := ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- The second chart retains the matching full line with its original signed scale. -/
@[reassoc] theorem initialGlobalFirstComponent_right :
    ProjectiveLine.right K ≫
      initialGlobalFirstComponent hπ data D h1 hstart hk r hr =
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ G₁ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

/-- The zero endpoint is the original first conic parameter origin. -/
@[reassoc] theorem initialGlobalFirstComponent_zero :
    ProjectiveLine.zero K ≫
      initialGlobalFirstComponent hπ data D h1 hstart hk r hr =
      initialGlobalFirstSection hπ data D (1 + r) hr hstart (by omega) := by
  rw [ProjectiveLine.zero, Category.assoc, initialGlobalFirstComponent_left,
    ← Category.assoc, conicZeroAffineIso_origin,
    initialGlobalConicFirstParameter_origin]

/-- The infinity endpoint is the next original first retained node. -/
@[reassoc] theorem initialGlobalFirstComponent_infinity :
    ProjectiveLine.infinity K ≫
        initialGlobalFirstComponent hπ data D h1 hstart hk r hr =
      olderGlobalFirstSection hπ data D 0 h1 r hr hstart hk := by
  rw [ProjectiveLine.infinity, Category.assoc, initialGlobalFirstComponent_right,
    ← Category.assoc, ProjectiveLine.chartZero_chartScaling]
  exact olderGlobalFirstSection_line hπ data D 0 h1 r hr hstart hk

/-- The full second parameter meets its next line with the original reciprocal scale. -/
theorem initialGlobalSecondComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ (E).hom ≫ P₂ =
      Spec.map (CommRingCat.ofHom
        (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹))) ≫
          ProjectiveLine.overlapLeft K ≫ G₂ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  exact initialGlobalSecondParameter_overlap hπ data D h1 hstart hk r hr

/-- The complete second projective component retained in the actual global model. -/
def initialGlobalSecondComponent :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (1 + r) hr :=
  ProjectiveLine.scaledReciprocalDesc (-tangent)⁻¹ ((E).hom ≫ P₂) G₂
    (initialGlobalSecondComponent_overlap hπ data D h1 hstart hk r hr)

/-- The first chart is the entire original second conic parameter. -/
@[reassoc] theorem initialGlobalSecondComponent_left :
    ProjectiveLine.left K ≫
      initialGlobalSecondComponent hπ data D h1 hstart hk r hr =
      (E).hom ≫ P₂ := ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- The second chart retains the matching full line with its original signed scale. -/
@[reassoc] theorem initialGlobalSecondComponent_right :
    ProjectiveLine.right K ≫
      initialGlobalSecondComponent hπ data D h1 hstart hk r hr =
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ G₂ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

/-- The zero endpoint is the original second conic parameter origin. -/
@[reassoc] theorem initialGlobalSecondComponent_zero :
    ProjectiveLine.zero K ≫
      initialGlobalSecondComponent hπ data D h1 hstart hk r hr =
      initialGlobalSecondSection hπ data D (1 + r) hr hstart (by omega) := by
  rw [ProjectiveLine.zero, Category.assoc, initialGlobalSecondComponent_left,
    ← Category.assoc, conicZeroAffineIso_origin,
    initialGlobalConicSecondParameter_origin]

/-- The infinity endpoint is the next original second retained node. -/
@[reassoc] theorem initialGlobalSecondComponent_infinity :
    ProjectiveLine.infinity K ≫
        initialGlobalSecondComponent hπ data D h1 hstart hk r hr =
      olderGlobalSecondSection hπ data D 0 h1 r hr hstart hk := by
  rw [ProjectiveLine.infinity, Category.assoc, initialGlobalSecondComponent_right,
    ← Category.assoc, ProjectiveLine.chartZero_chartScaling]
  exact olderGlobalSecondSection_line hπ data D 0 h1 r hr hstart hk

end FLT.Mazur.WeierstrassDividedDepth

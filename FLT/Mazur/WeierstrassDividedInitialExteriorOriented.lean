/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialExteriorProjective
public import FLT.Mazur.ProjectiveLineSlopeNormalizationCharts

/-!
# The ordered initial exterior component

Normalize the actual initial component so its first original node is zero
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth) (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "u" => Units.mk0 a (IsUnit.ne_zero (residue_tangent_isUnit D))
local notation "E" => initialExteriorCurve hπ data D j hj hstart hk
local notation "e" => initialExteriorProjectiveIso hπ data D j hj hstart hk hdepth

/-- The actual initial exterior component with ordered polygon endpoints. -/
def initialExteriorOrientedIso : E ≅ ProjectiveLine.scheme K :=
  e ≪≫ ProjectiveLine.slopeNormalizationIso u

/-- The normalization is over the original residue field. -/
@[reassoc] theorem initialExteriorOrientedIso_structure :
    (initialExteriorOrientedIso hπ data D j hj hstart hk hdepth).hom ≫
      ProjectiveLine.toBase K = initialExteriorStructure hπ data D j hj hstart hk := by
  rw [initialExteriorOrientedIso, Iso.trans_hom, Category.assoc,
    ProjectiveLine.slopeNormalizationIso_base, initialExteriorProjectiveIso_structure]

/-- The entire original affine incidence chart uses the proved projective normalization. -/
@[reassoc] theorem initialExteriorOrientedIso_affine :
    initialExteriorAffineChart hπ data D j hj hstart hk ≫
      (initialExteriorOrientedIso hπ data D j hj hstart hk hdepth).hom =
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom := by
  rw [initialExteriorOrientedIso, Iso.trans_hom,
    initialExteriorProjectiveIso_affine_assoc]

/-- The entire original infinity torus has the standard reciprocal left coordinate. -/
@[reassoc] theorem initialExteriorOrientedIso_laurent :
    initialExteriorLaurentChart hπ data D j hj hstart hk hdepth ≫
      (initialExteriorOrientedIso hπ data D j hj hstart hk hdepth).hom =
        ProjectiveLine.overlapRight K ≫ ProjectiveLine.left K := by
  rw [initialExteriorOrientedIso, Iso.trans_hom,
    initialExteriorProjectiveIso_laurent_assoc,
    ProjectiveLine.slopeNormalization_infinityTorus_left]

/-- The normalized projective component still maps into the original global residue model. -/
def initialOrientedToGlobal : ProjectiveLine.scheme K ⟶
    finiteGlobalTensorModel hπ data K j hj :=
  (initialExteriorOrientedIso hπ data D j hj hstart hk hdepth).inv ≫
    initialExteriorToGlobal hπ data D j hj hstart hk

/-- The normalized map is the original projective component map with its inverse coordinates. -/
theorem initialOrientedToGlobal_eq :
    initialOrientedToGlobal hπ data D j hj hstart hk hdepth =
      (ProjectiveLine.slopeNormalizationIso u).inv ≫
        initialProjectiveToGlobal hπ data D j hj hstart hk hdepth := by
  simp only [initialOrientedToGlobal, initialExteriorOrientedIso, Iso.trans_inv,
    initialProjectiveToGlobal, Category.assoc]

/-- The polygon zero endpoint is the original first initial node, as a scheme section. -/
@[reassoc] theorem initialOrientedToGlobal_zero :
    ProjectiveLine.zero K ≫ initialOrientedToGlobal hπ data D j hj hstart hk hdepth =
      initialGlobalFirstSection hπ data D j hj hstart hk := by
  rw [initialOrientedToGlobal_eq, ProjectiveLine.slopeNormalization_inv_zero_assoc]
  exact initialProjectiveToGlobal_first hπ data D j hj hstart hk hdepth

/-- The polygon infinity endpoint is the original second initial node. -/
@[reassoc] theorem initialOrientedToGlobal_infinity :
    ProjectiveLine.infinity K ≫ initialOrientedToGlobal hπ data D j hj hstart hk hdepth =
      initialGlobalSecondSection hπ data D j hj hstart hk := by
  rw [initialOrientedToGlobal_eq, ProjectiveLine.slopeNormalization_inv_infinity_assoc]
  exact initialProjectiveToGlobal_second hπ data D j hj hstart hk hdepth

/-- The normalized component retains the actual global coefficient projection. -/
@[reassoc] theorem initialOrientedToGlobal_structure :
    initialOrientedToGlobal hπ data D j hj hstart hk hdepth ≫
      CategoryTheory.Limits.pullback.fst _ _ = ProjectiveLine.toBase K := by
  rw [initialOrientedToGlobal, Category.assoc, ← initialExteriorStructure,
    ← initialExteriorOrientedIso_structure hπ data D j hj hstart hk hdepth,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth

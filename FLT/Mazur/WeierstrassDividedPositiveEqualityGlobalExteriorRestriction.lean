/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalInitialRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalInitialRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalAtlasDesc
import all FLT.Mazur.WeierstrassDividedInitialExteriorCurve

/-!
# Global descent on the complete exterior component

The original incidence line and infinity tensor chart determine the exterior
by its actual pushout. Both restrictions retain the slope normalization.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => positiveEqualityCycleGlobalDesc hπ data D s hs hstart hk hp F w
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "t" => Units.mk0 (residue R W.a₁) (IsUnit.ne_zero (residue_tangent_isUnit D))
local notation "E" => initialExteriorOrientedIso hπ data D (s + 1) hs hstart
  (by omega) (by omega)
local notation "ι" => initialExteriorInfinityChart hπ data D (s + 1) hs hstart (by omega)

/-- The complete incidence chart recovers its normalized exterior map. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_incidence :
    ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ (Z 0).left ≫ d =
      ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 := by
  rw [positiveEqualityCycleComponent_incidence_chart_assoc]
  simp only [initialGlobalIncidenceLine, initialGlobalResidueFiberChart, Category.assoc]
  rw [positiveEqualityCycleGlobalDesc_initial_tensor]
  exact positiveEqualityInitialTensorDesc_incidence hπ data D s hs hstart hk F w

/-- The unchanged full infinity chart recovers the same exterior map. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_infinity :
    ι ≫ (E).hom ≫ (Z 0).left ≫ d = ι ≫ (E).hom ≫ F 0 := by
  rw [positiveEqualityCycleComponent_infinity_chart_assoc]
  change globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ d = _
  rw [positiveEqualityCycleGlobalDesc_atlas, positiveEqualityCycleAtlasFamily_infinity]
  rfl

/-- Descent recovers the entire exterior, including both original nodes and infinity. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_exterior_component :
    (Z 0).left ≫ d = F 0 := by
  apply (cancel_epi (E).hom).mp
  apply pushout.hom_ext
  · change initialExteriorAffineChart hπ data D (s + 1) hs hstart (by omega) ≫
      (E).hom ≫ (Z 0).left ≫ d =
        initialExteriorAffineChart hπ data D (s + 1) hs hstart (by omega) ≫ (E).hom ≫ F 0
    rw [initialExteriorOrientedIso_affine_assoc, initialExteriorOrientedIso_affine_assoc]
    exact positiveEqualityCycleGlobalDesc_incidence hπ data D s hs hstart hk hp F w
  · exact positiveEqualityCycleGlobalDesc_infinity hπ data D s hs hstart hk hp F w

end FLT.Mazur.WeierstrassDividedDepth

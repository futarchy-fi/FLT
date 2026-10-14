/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionSmoothLift
public import FLT.Mazur.PolygonCompleteIdentityActionSectionProj

/-!
# The full smooth-input lift preserves the original contraction square

It agrees with the previous lift on its whole unchanged domain and commutes
with the canonical map to the original full marking section ring's Proj.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart SectionGradedSum SectionGradedProjConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "U" => completePointIdentityOpen K n h (0 : Fin n)
local notation "V" => completeIdentityActionUnchangedOpen K n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)

/-- The exact inclusion of the former lift domain into the full smooth-input domain. -/
def completeIdentityActionUnchangedToSmooth :
    (V).toScheme ⟶ (completeIdentityActionSmoothOpen K n h).toScheme :=
  (completeIdentityActionProduct K n h 0).homOfLE
    (completeIdentityActionUnchangedOpen_le_smooth K n h)

/-- Its inclusion into the original whole action product is unchanged. -/
@[reassoc] theorem completeIdentityActionUnchangedToSmooth_inclusion :
    completeIdentityActionUnchangedToSmooth K n h ≫
      (completeIdentityActionSmoothOpen K n h).ι = (V).ι := Scheme.homOfLE_ι _ _

/-- The new lift on the old domain has an actual coordinate in the original identity open. -/
def completeIdentityActionSmoothUnchangedCoordinate : (V).toScheme ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι
    (completeIdentityActionUnchangedToSmooth K n h ≫ completeIdentityActionSmoothLift K n h)
    (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      change ((completeIdentityActionUnchangedToSmooth K n h ≫
        completeIdentityActionSmoothLift K n h) ≫ (g)) x ∈
          integralSmoothOpen (completePointWeierstrassCurve K n h 0)
      rw [Category.assoc, completeIdentityActionSmoothLift_contraction,
        completeIdentityActionUnchangedToSmooth_inclusion_assoc]
      exact x.2)

/-- Both constructed lifts agree on the entire original unchanged-input domain. -/
@[reassoc] theorem completeIdentityActionSmoothLift_unchanged :
    completeIdentityActionUnchangedToSmooth K n h ≫ completeIdentityActionSmoothLift K n h =
      completeIdentityActionUnchangedLift K n h 0 ≫ (U).ι := by
  have hc : completeIdentityActionSmoothUnchangedCoordinate K n h ≫ (U).ι =
      completeIdentityActionUnchangedToSmooth K n h ≫ completeIdentityActionSmoothLift K n h :=
    IsOpenImmersion.lift_fac _ _ _
  have he : completeIdentityActionSmoothUnchangedCoordinate K n h =
      completeIdentityActionUnchangedLift K n h 0 := by
    apply completeIdentityActionUnchangedLift_unique
    rw [← Category.assoc, hc, Category.assoc, completeIdentityActionSmoothLift_contraction,
      completeIdentityActionUnchangedToSmooth_inclusion_assoc]
  rw [← hc, he]

local notation "L" => completePointLine K n h (0 : Fin n)
local instance completeIdentitySmoothCompatibilityLine : Fact (LocallyFreeRankOne (L)) :=
  ⟨completePointLine_locallyFreeRankOne K n h 0⟩

/-- Every original smooth input retains the canonical full marking-section Proj square. -/
@[reassoc] theorem completeIdentityActionSmoothLift_sectionProj :
    completeIdentityActionSmoothLift K n h ≫
      toProj (L) (completePointLine_positivePowerGenerated K n h 0) =
        (completeIdentityActionSmoothOpen K n h).ι ≫
          completeIdentityActionSectionProjTarget K n h 0 := by
  apply (cancel_mono (completePointCanonicalCubicIso K n h 0).hom).mp
  simp only [Category.assoc, completePointCanonicalCubicIso_contraction,
    completeIdentityActionSectionProjTarget_cubic, completeIdentityActionSmoothLift_contraction]

end FLT.Mazur.PolygonInfinitesimalStages

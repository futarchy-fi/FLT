/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAffineQuotientStage
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The original generic action on an arbitrary affine input

Inverting the affine input's actual parameter puts its entire second input
in the already constructed smooth action domain. This constructs the generic
polygon-valued lift with the unchanged original cubic equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {A : Type} [CommRing A] (v : Spec (.of A) ⟶ completeIdentityActionProduct K n h 0)
local notation "ρ" => completeIdentityAffineScalars K n h v
local notation "t" => (ρ) PowerSeries.X
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (t))))
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "U" => completeIdentityActionSmoothOpen K n h

/-- Every point after inverting the original affine parameter belongs to the smooth input. -/
theorem completeIdentityGenericAffine_mem (x : Spec (.of (Localization.Away (t)))) :
    ((g) ≫ v) x ∈ (U) := by
  apply complete_mem_smoothLocus_of_parameter_notMem
  have he : (g) ≫ v ≫ (s) ≫ (π) =
      Spec.map (CommRingCat.ofHom ((algebraMap A (Localization.Away (t))).comp (ρ))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, completeIdentityAffineScalars,
      CommRingCat.ofHom_hom, Spec.map_preimage]
  have hp := congrArg (fun k ↦ k x) he
  change (π) ((s) (v ((g) x))) = _ at hp
  change PowerSeries.X ∉ ((π) ((s) (v ((g) x)))).asIdeal
  rw [hp]
  exact x.asIdeal.notMem_of_isUnit (IsLocalization.Away.algebraMap_isUnit (t))

/-- Extract the actual smooth-input point from the original localized affine source. -/
def completeIdentityGenericAffineToSmooth :
    Spec (.of (Localization.Away (t))) ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι ((g) ≫ v) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, completeIdentityGenericAffine_mem K n h v x⟩, rfl⟩)

/-- The extracted smooth input retains its original localized source map. -/
@[reassoc] theorem completeIdentityGenericAffineToSmooth_input :
    completeIdentityGenericAffineToSmooth K n h v ≫ (U).ι = (g) ≫ v :=
  IsOpenImmersion.lift_fac _ _ _

/-- The existing smooth action constructs the entire original generic affine action. -/
def completeIdentityGenericAffineLift :
    Spec (.of (Localization.Away (t))) ⟶ exactVeroneseProj K n h :=
  completeIdentityGenericAffineToSmooth K n h v ≫ completeIdentityActionSmoothLift K n h

/-- The constructed generic action preserves the original cubic equation. -/
@[reassoc] theorem completeIdentityGenericAffineLift_cubic :
    completeIdentityGenericAffineLift K n h v ≫ completePointToIntegralCubic K n h 0 =
      (g) ≫ v ≫ completeIdentityActionTarget K n h 0 := by
  rw [completeIdentityGenericAffineLift, Category.assoc,
    completeIdentityActionSmoothLift_contraction, completeIdentityGenericAffineToSmooth_input_assoc]

end FLT.Mazur.PolygonInfinitesimalStages

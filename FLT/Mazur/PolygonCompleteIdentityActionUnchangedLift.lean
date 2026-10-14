/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionTarget
public import FLT.Mazur.WeierstrassUniversalTranslationSmoothLocus

/-!
# The actual action lift on the entire unchanged contraction domain

The original restricted contraction supplies the lift, and universal smooth
locus invariance identifies its exact source open. No lift is assumed at a
contracted input; extending across those inputs remains a separate construction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "π" => exactVeroneseProjToBase K n h
local notation "U" => completePointIdentityOpen K n h i
local notation "e" => completePointSmoothCubicIso K n h i
local notation "a" => completeIdentityActionTarget K n h i

/-- The full open on which the contraction-side action has smooth cubic output. -/
abbrev completeIdentityActionUnchangedOpen : (completeIdentityActionProduct K n h i).Opens :=
  (a) ⁻¹ᵁ integralSmoothOpen (W)

/-- This is exactly the original second input's identity open, without shrinking it. -/
theorem completeIdentityActionUnchangedOpen_eq :
    completeIdentityActionUnchangedOpen K n h i =
      pullback.snd (G).X.hom (π) ⁻¹ᵁ (U) := by
  change ((completeIdentityActionToCubicProduct K n h i ≫ leftSmoothFactorAddition (W))
    ⁻¹ᵁ integralSmoothOpen (W)) = _
  rw [Scheme.Hom.comp_preimage, leftSmoothFactorAddition_preimage_smooth,
    ← Scheme.Hom.comp_preimage, completeIdentityActionToCubicProduct_snd,
    Scheme.Hom.comp_preimage]

local notation "V" => completeIdentityActionUnchangedOpen K n h i

/-- The constructed lift into the original identity open on its entire unchanged domain. -/
def completeIdentityActionUnchangedLift : (V).toScheme ⟶ (U).toScheme :=
  ((a) ∣_ integralSmoothOpen (W)) ≫ (e).inv

/-- The lift uses the actual original contraction, as a scheme morphism. -/
@[reassoc] theorem completeIdentityActionUnchangedLift_contraction :
    completeIdentityActionUnchangedLift K n h i ≫ (U).ι ≫ (g) = (V).ι ≫ (a) := by
  rw [completeIdentityActionUnchangedLift, Category.assoc,
    ← completePointSmoothCubicIso_inclusion, Iso.inv_hom_id_assoc, morphismRestrict_ι]

/-- The lift retains the original complete-base structure map. -/
@[reassoc] theorem completeIdentityActionUnchangedLift_structure :
    completeIdentityActionUnchangedLift K n h i ≫ (U).ι ≫ (π) =
      (V).ι ≫ pullback.snd (G).X.hom (π) ≫ (π) := by
  apply (cancel_mono (Scheme.toSpecΓ (Spec (.of (PowerSeries K))))).mp
  simp only [Category.assoc]
  rw [← completePointToIntegralCubic_over,
    completeIdentityActionUnchangedLift_contraction_assoc,
    completeIdentityActionTarget_structure, completePointToIntegralCubic_over]

/-- The unchanged original open admits exactly this lift of the constructed cubic target. -/
theorem completeIdentityActionUnchangedLift_unique (f : (V).toScheme ⟶ (U).toScheme)
    (hf : f ≫ (U).ι ≫ (g) = (V).ι ≫ (a)) :
    f = completeIdentityActionUnchangedLift K n h i := by
  apply (cancel_mono (e).hom).mp
  apply (cancel_mono (integralSmoothOpen (W)).ι).mp
  simpa only [Category.assoc, completePointSmoothCubicIso_inclusion,
    completeIdentityActionUnchangedLift_contraction] using hf

end FLT.Mazur.PolygonInfinitesimalStages

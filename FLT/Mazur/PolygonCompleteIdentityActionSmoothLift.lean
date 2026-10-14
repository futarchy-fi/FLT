/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentitySmoothActionEquivariance
public import FLT.Mazur.PolygonCompleteIdentityActionUnchangedLift

/-!
# A constructed lift on every original smooth second input

The original action product's full smooth-input open carries a polygon-valued
lift, including smooth points on contracted components. Singular inputs remain.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "π" => exactVeroneseProjToBase K n h
/-- The original whole second input, without any restriction to the smooth locus. -/
abbrev completeIdentityActionSecond :
    completeIdentityActionProduct K n h 0 ⟶ exactVeroneseProj K n h :=
  pullback.snd (G).X.hom (π)

local notation "s" => completeIdentityActionSecond K n h
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)

/-- The entire open of the original action product with a smooth second input. -/
abbrev completeIdentityActionSmoothOpen : (completeIdentityActionProduct K n h 0).Opens :=
  (s) ⁻¹ᵁ (π).smoothLocus

local notation "V" => completeIdentityActionSmoothOpen K n h

/-- The actual smooth inputs extracted from the original unchanged action product. -/
def completeIdentityActionSmoothCoordinates : (V).toScheme ⟶ ((G).X ⊗ (M)).left :=
  pullback.lift ((V).ι ≫ pullback.fst (G).X.hom (π)) ((s) ∣_ (π).smoothLocus) (by
    change ((V).ι ≫ pullback.fst (G).X.hom (π)) ≫ (G).X.hom =
      ((s) ∣_ (π).smoothLocus) ≫ (π).smoothLocus.ι ≫ (π)
    rw [morphismRestrict_ι_assoc, Category.assoc, pullback.condition])

/-- The extracted coordinates reconstruct the exact original input pair. -/
@[reassoc] theorem completeIdentityActionSmoothCoordinates_input :
    completeIdentityActionSmoothCoordinates K n h ≫ completeIdentitySmoothActionInput K n h =
      (V).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentitySmoothActionInput_fst,
      completeIdentityActionSmoothCoordinates, pullback.lift_fst]
  · rw [Category.assoc, completeIdentitySmoothActionInput_snd,
      ← Category.assoc, completeIdentityActionSmoothCoordinates,
      pullback.lift_snd, morphismRestrict_ι]

/-- The constructed polygon-valued lift on every original smooth second input. -/
def completeIdentityActionSmoothLift : (V).toScheme ⟶ exactVeroneseProj K n h :=
  completeIdentityActionSmoothCoordinates K n h ≫
    (completeIdentitySmoothAction K n h).left ≫ (π).smoothLocus.ι

/-- The full smooth-input lift retains the original cubic action target. -/
@[reassoc] theorem completeIdentityActionSmoothLift_contraction :
    completeIdentityActionSmoothLift K n h ≫ (g) = (V).ι ≫ (a) := by
  rw [completeIdentityActionSmoothLift, Category.assoc, Category.assoc,
    completeIdentitySmoothAction_contraction, completeIdentityActionSmoothCoordinates_input_assoc]

/-- The full smooth-input lift retains the literal original power-series base. -/
@[reassoc] theorem completeIdentityActionSmoothLift_structure :
    completeIdentityActionSmoothLift K n h ≫ (π) = (V).ι ≫ (s) ≫ (π) := by
  apply (cancel_mono (Scheme.toSpecΓ (Spec (.of (PowerSeries K))))).mp
  simp only [Category.assoc]
  rw [← completePointToIntegralCubic_over,
    completeIdentityActionSmoothLift_contraction_assoc,
    completeIdentityActionTarget_structure, completePointToIntegralCubic_over]

/-- The new lift's domain contains the entire previously constructed unchanged-input domain. -/
theorem completeIdentityActionUnchangedOpen_le_smooth :
    completeIdentityActionUnchangedOpen K n h 0 ≤ completeIdentityActionSmoothOpen K n h := by
  rw [completeIdentityActionUnchangedOpen_eq]
  intro x hx
  exact completePointIdentityOpen_le_smooth K n h 0 hx

end FLT.Mazur.PolygonInfinitesimalStages

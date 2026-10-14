/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentitySmoothAction

/-!
# Exact identity coordinates inside the full smooth action product

The entire preimage of the second identity open has constructed pair
coordinates. These retain both original input maps without shrinking the open.
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
local notation "U" => completePointIdentityOpen K n h (0 : Fin n)
local notation "j" => completeIdentityChart K n h (0 : Fin n) 0
/-- The original second input of the smooth action product, in the whole polygon. -/
abbrev completeIdentitySmoothSecond : ((G).X ⊗ (M)).left ⟶ exactVeroneseProj K n h :=
  pullback.snd (G).X.hom (M).hom ≫ (π).smoothLocus.ι

local notation "p" => completeIdentitySmoothSecond K n h

/-- The full original open where the second smooth input is in the identity chart. -/
abbrev completeIdentitySmoothActionCoordinateOpen : ((G).X ⊗ (M)).left.Opens :=
  (p) ⁻¹ᵁ (U)

local notation "V" => completeIdentitySmoothActionCoordinateOpen K n h

/-- Actual pair coordinates on the entire second-identity preimage. -/
def completeIdentitySmoothActionCoordinates : (V).toScheme ⟶ ((G).X ⊗ (G).X).left :=
  pullback.lift ((V).ι ≫ pullback.fst (G).X.hom (M).hom) ((p) ∣_ (U)) (by
    have hr : ((p) ∣_ (U)) ≫ (G).X.hom = (V).ι ≫ (p) ≫ (π) := by
      rw [completePointOriginalBaseGroup_structure, morphismRestrict_ι_assoc]
    have he : pullback.fst (G).X.hom (M).hom ≫ (G).X.hom = (p) ≫ (π) :=
      pullback.condition.trans (Category.assoc _ _ _).symm
    exact (Category.assoc _ _ _).trans ((congrArg ((V).ι ≫ ·) he).trans hr.symm))

/-- The pair coordinates retain their first input. -/
@[reassoc] theorem completeIdentitySmoothActionCoordinates_fst :
    completeIdentitySmoothActionCoordinates K n h ≫ pullback.fst _ _ =
      (V).ι ≫ pullback.fst (G).X.hom (M).hom := pullback.lift_fst _ _ _

/-- Their second coordinate is the actual original morphism restriction. -/
@[reassoc] theorem completeIdentitySmoothActionCoordinates_snd :
    completeIdentitySmoothActionCoordinates K n h ≫ pullback.snd _ _ =
      (p) ∣_ (U) := pullback.lift_snd _ _ _

/-- The pair coordinates reconstruct the unchanged smooth input pair. -/
@[reassoc] theorem completeIdentitySmoothActionCoordinates_inclusion :
    completeIdentitySmoothActionCoordinates K n h ≫ (𝟙 (G).X ⊗ₘ (j)).left = (V).ι := by
  apply pullback.hom_ext
  · have he := congrArg Over.Hom.left
      (CartesianMonoidalCategory.tensorHom_fst (𝟙 (G).X) (j))
    change (𝟙 (G).X ⊗ₘ (j)).left ≫ pullback.fst (G).X.hom (M).hom =
      pullback.fst (G).X.hom (G).X.hom ≫ 𝟙 _ at he
    rw [Category.comp_id] at he
    rw [Category.assoc, he, completeIdentitySmoothActionCoordinates_fst]
  · apply (cancel_mono (π).smoothLocus.ι).mp
    have he := congrArg Over.Hom.left
      (CartesianMonoidalCategory.tensorHom_snd (𝟙 (G).X) (j))
    change (𝟙 (G).X ⊗ₘ (j)).left ≫ pullback.snd (G).X.hom (M).hom =
      pullback.snd (G).X.hom (G).X.hom ≫ (j).left at he
    have he' : (𝟙 (G).X ⊗ₘ (j)).left ≫
        pullback.snd (G).X.hom (M).hom ≫ (π).smoothLocus.ι =
        pullback.snd (G).X.hom (G).X.hom ≫ (U).ι := by
      rw [← Category.assoc, he, Category.assoc, completeIdentityChart_zero_inclusion]
    simp only [Category.assoc, he', completeIdentitySmoothActionCoordinates_snd_assoc,
      morphismRestrict_ι]

end FLT.Mazur.PolygonInfinitesimalStages

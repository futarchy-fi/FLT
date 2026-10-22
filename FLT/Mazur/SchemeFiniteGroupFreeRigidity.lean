/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeUnramified
public import FLT.Mazur.SchemeFiniteGroupFreeFlat
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Original scheme rigidity for free finite-group quotients

Field-valued freeness proves formal unramifiedness of the actual affine
quotient map. Arbitrary coefficient base changes retain this rigidity, so
agreement on a nilpotent closed test determines a unique full arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction
namespace FLT.Mazur.SchemeFiniteGroupQuotient
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [IsAffine X]
  (ρ : G →* Aut X)
  (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) (g : G),
    a ≫ (ρ g).hom = a → g = 1)
include hfree

/-- The unchanged free quotient map is rigid on full nonreduced coefficient tests. -/
theorem quotientMap_formallyUnramified_of_free : FormallyUnramified (quotientMap ρ) := by
  let _ := coordinateAction ρ
  let _ := FiniteGroupQuotient.invariant_formallyUnramified G Γ(X, ⊤)
    (coordinate_fixedPointIdeal_eq_top ρ hfree)
  let _ : FormallyUnramified (FiniteGroupQuotient.quotientMap G Γ(X, ⊤)) :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr
      (RingHom.formallyUnramified_algebraMap.mpr inferInstance)
  change FormallyUnramified (X.toSpecΓ ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤))
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

/-- The rigidity survives every coefficient base change, including nonflat ones. -/
theorem freeQuotient_baseChange_formallyUnramified {B : Scheme.{u}} (b : B ⟶ quotient ρ) :
    FormallyUnramified (pullback.snd (quotientMap ρ) b) := by
  let _ := quotientMap_formallyUnramified_of_free ρ hfree
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- A nilpotent closed test detects full arrows into the actual free quotient source. -/
theorem freeQuotient_nilpotent_hom_ext {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (hi : IsNilpotent i.ker) (a b : T ⟶ X)
    (hab : i ≫ a = i ≫ b) (hs : a ≫ quotientMap ρ = b ≫ quotientMap ρ) : a = b := by
  let _ := quotientMap_formallyUnramified_of_free ρ hfree
  exact FormallyUnramified.hom_ext i hi (quotientMap ρ) hab hs

end FLT.Mazur.SchemeFiniteGroupQuotient

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeEtale
public import FLT.Mazur.SchemeFiniteGroupFreeRigidity
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Etale covers from field-valued freeness

The affine quotient of a free finite action is finite etale. Its arbitrary
base changes give actual surjective etale charts, with the existing faithful
descent on full nonreduced coefficient rings.
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

/-- The actual affine quotient map is etale without an assumed coefficient presentation. -/
theorem quotientMap_etale_of_free : Etale (quotientMap ρ) := by
  let _ := coordinateAction ρ
  let _ := FiniteGroupQuotient.invariant_etale G Γ(X, ⊤)
    (coordinate_fixedPointIdeal_eq_top ρ hfree)
  let _ : Etale (FiniteGroupQuotient.quotientMap G Γ(X, ⊤)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  change Etale (X.toSpecΓ ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤))
  infer_instance

/-- Every coefficient base change is a surjective etale cover of the original coefficient scheme. -/
theorem freeQuotient_baseChange_etale {B : Scheme.{u}} (b : B ⟶ quotient ρ) :
    Etale (pullback.snd (quotientMap ρ) b) := by
  let _ := quotientMap_etale_of_free ρ hfree
  infer_instance

end FLT.Mazur.SchemeFiniteGroupQuotient

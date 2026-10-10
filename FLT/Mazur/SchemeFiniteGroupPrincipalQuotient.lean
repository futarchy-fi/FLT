/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotientMaps
public import FLT.Mazur.FiniteGroupOpenRestriction
public import FLT.Mazur.InvariantLocalizationComparison

/-!
# Principal opens in actual affine scheme quotients

An invariant global function cuts out a stable principal open. Its restricted
scheme action has the expected localization on fixed rings, so the induced
quotient map is a scheme open immersion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] {X : Scheme.{u}} (ρ : G →* Aut X)
variable (r : invariantCoordinates ρ)

/-- An invariant function defines a stable principal open in the original scheme. -/
lemma basicOpen_stable (g : G) :
    (ρ g).hom ⁻¹ᵁ X.basicOpen (r : Γ(X, ⊤)) = X.basicOpen (r : Γ(X, ⊤)) := by
  rw [Scheme.preimage_basicOpen_top]
  congr 1
  have h := r.property g⁻¹
  change coordinateHom ρ g⁻¹ (r : Γ(X, ⊤)) = (r : Γ(X, ⊤)) at h
  simpa only [coordinateHom, inv_inv] using h

/-- The actual action on the stable principal open. -/
def principalAction : G →* Aut (X.basicOpen (r : Γ(X, ⊤))).toScheme :=
  FiniteGroupRestriction.restrictedAction ρ _ (basicOpen_stable ρ r)

/-- The principal-open immersion is equivariant for the constructed action. -/
@[reassoc]
lemma principal_ι_equivariant (g : G) :
    (principalAction ρ r g).hom ≫ (X.basicOpen (r : Γ(X, ⊤))).ι =
      (X.basicOpen (r : Γ(X, ⊤))).ι ≫ (ρ g).hom :=
  FiniteGroupRestriction.restrictedAction_hom_ι ρ _ (basicOpen_stable ρ r) g

/-- The map from the quotient of the stable principal open into the original quotient. -/
def principalQuotientMap : quotient (principalAction ρ r) ⟶ quotient ρ :=
  quotientHom (principalAction ρ r) ρ (X.basicOpen (r : Γ(X, ⊤))).ι
    (principal_ι_equivariant ρ r)

/-- Fixed-ring localization proves a scheme open immersion, not just a pointwise embedding. -/
instance principalQuotientMap_isOpenImmersion [Finite G] [IsAffine X] :
    IsOpenImmersion (principalQuotientMap ρ r) := by
  let _ := coordinateAction ρ
  let _ := coordinateAction (principalAction ρ r)
  let U := X.basicOpen (r : Γ(X, ⊤))
  have he (g : G) (a : Γ(X, ⊤)) :
      g • algebraMap Γ(X, ⊤) Γ(U, ⊤) a = algebraMap Γ(X, ⊤) Γ(U, ⊤) (g • a) := by
    exact congrArg (fun k : Γ(X, ⊤) →+* Γ(U, ⊤) ↦ k a)
      (coordinateHom_comp (principalAction ρ r) ρ U.ι (principal_ι_equivariant ρ r) g)
  let _ := (FiniteGroupQuotient.invariantLocalizationMap G Γ(X, ⊤) Γ(U, ⊤) he).toAlgebra
  let _ := FiniteGroupQuotient.invariants_away G Γ(X, ⊤) Γ(U, ⊤) he r
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (invariantCoordinates ρ) (invariantCoordinates (principalAction ρ r)))))
  exact IsOpenImmersion.of_isLocalization r

end FLT.Mazur.SchemeFiniteGroupQuotient

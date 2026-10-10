/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCoordinateAction
public import FLT.Mazur.FiniteGroupAffineQuotient

/-!
# Invariant-coordinate quotients of affine schemes

Apply the affine invariant-ring quotient to an actual scheme action via its
constructed action on global sections. No presentation of the affine scheme
as a particular spectrum is required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] {X : Scheme.{u}} (ρ : G →* Aut X)

/-- The actual fixed subring of global functions for the inverse-pullback action. -/
abbrev invariantCoordinates : Type u :=
  let _ := coordinateAction ρ
  FiniteGroupQuotient.invariantRing G Γ(X, ⊤)

/-- The spectrum of invariant coordinates. -/
def quotient : Scheme.{u} := Spec (.of (invariantCoordinates ρ))

/-- The quotient map transported along the canonical map to the spectrum of sections. -/
def quotientMap : X ⟶ quotient ρ :=
  let _ := coordinateAction ρ
  X.toSpecΓ ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤)

/-- The actual scheme map is invariant under the original automorphisms. -/
@[reassoc]
lemma quotientMap_invariant (g : G) : (ρ g).hom ≫ quotientMap ρ = quotientMap ρ := by
  let _ := coordinateAction ρ
  change (ρ g).hom ≫ (X.toSpecΓ ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤)) = _
  rw [← Category.assoc, toSpecΓ_equivariant, Category.assoc]
  change X.toSpecΓ ≫ (FiniteGroupQuotient.actionMap G Γ(X, ⊤) g⁻¹ ≫
    FiniteGroupQuotient.quotientMap G Γ(X, ⊤)) = _
  rw [FiniteGroupQuotient.actionMap_quotientMap]
  rfl

/-- For an affine scheme and a finite group the constructed quotient map is integral. -/
instance quotientMap_integral [Finite G] [IsAffine X] : IsIntegralHom (quotientMap ρ) := by
  let _ := coordinateAction ρ
  change IsIntegralHom (X.toSpecΓ ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤))
  infer_instance

/-- Every point of the affine invariant quotient has a preimage in the original scheme. -/
instance quotientMap_surjective [Finite G] [IsAffine X] : Surjective (quotientMap ρ) := by
  let _ := coordinateAction ρ
  change Surjective (X.toSpecΓ ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤))
  infer_instance

end FLT.Mazur.SchemeFiniteGroupQuotient

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotient

/-!
# Functorial maps between invariant-coordinate quotients

An equivariant scheme map gives a map of fixed rings and hence a map of the
actual quotient spectra. These maps respect composition and the quotient maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] {X Y Z : Scheme.{u}}
variable (ρ : G →* Aut X) (τ : G →* Aut Y)
variable (f : X ⟶ Y) (hf : ∀ g : G, (ρ g).hom ≫ f = f ≫ (τ g).hom)

/-- Pullback of invariant functions along the actual equivariant scheme map. -/
def invariantMap : invariantCoordinates τ →+* invariantCoordinates ρ := by
  let _ := coordinateAction ρ
  let _ := coordinateAction τ
  refine (f.appTop.hom.comp (FiniteGroupQuotient.inclusion G Γ(Y, ⊤))).codRestrict
    (FixedPoints.subring Γ(X, ⊤) G) ?_
  intro a g
  change coordinateHom ρ g (f.appTop.hom (a : Γ(Y, ⊤))) = f.appTop.hom (a : Γ(Y, ⊤))
  have he := congrArg (fun k : Γ(Y, ⊤) →+* Γ(X, ⊤) ↦ k (a : Γ(Y, ⊤)))
    (coordinateHom_comp ρ τ f hf g)
  exact he.trans (congrArg f.appTop.hom (a.property g))

/-- The fixed-ring map is the original pullback on underlying functions. -/
@[simp]
lemma invariantMap_val (a : invariantCoordinates τ) :
    (invariantMap ρ τ f hf a : Γ(X, ⊤)) = f.appTop.hom (a : Γ(Y, ⊤)) := rfl

/-- The actual induced map between invariant-coordinate spectra. -/
def quotientHom : quotient ρ ⟶ quotient τ :=
  Spec.map (CommRingCat.ofHom (invariantMap ρ τ f hf))

/-- The quotient construction retains the original equivariant map. -/
@[reassoc]
lemma quotientMap_naturality : quotientMap ρ ≫ quotientHom ρ τ f hf = f ≫ quotientMap τ := by
  let _ := coordinateAction ρ
  let _ := coordinateAction τ
  unfold quotientMap quotientHom FiniteGroupQuotient.quotientMap
  rw [Category.assoc, ← Spec.map_comp, ← Category.assoc, Scheme.toSpecΓ_naturality,
    Category.assoc, ← Spec.map_comp]
  rfl

/-- Maps of quotient spectra satisfy the cocycle required on triple overlaps. -/
lemma quotientHom_comp (υ : G →* Aut Z) (k : Y ⟶ Z)
    (hk : ∀ g : G, (τ g).hom ≫ k = k ≫ (υ g).hom)
    (hfk : ∀ g : G, (ρ g).hom ≫ (f ≫ k) = (f ≫ k) ≫ (υ g).hom) :
    quotientHom ρ τ f hf ≫ quotientHom τ υ k hk = quotientHom ρ υ (f ≫ k) hfk := by
  unfold quotientHom
  rw [← Spec.map_comp]
  congr 1

end FLT.Mazur.SchemeFiniteGroupQuotient

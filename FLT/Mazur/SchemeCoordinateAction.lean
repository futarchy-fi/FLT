/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.CategoryTheory.Endomorphism

/-!
# The coordinate action of scheme automorphisms

Pullback by the inverse automorphism gives a left action on the actual global
sections. Equivariant scheme morphisms induce equivariant coordinate maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SchemeCoordinateAction

variable {G : Type*} [Group G] {X Y : Scheme} (ρ : G →* Aut X)

/-- The coordinate automorphism is pullback by the inverse group element. -/
def coordinateHom (g : G) : Γ(X, ⊤) →+* Γ(X, ⊤) := ((ρ g⁻¹).hom.appTop).hom

/-- Identity compatibility of the actual pullback. -/
lemma coordinateHom_one : coordinateHom ρ 1 = RingHom.id _ := by
  unfold coordinateHom
  rw [inv_one, map_one]
  rfl

/-- Inversion compensates for contravariance of the global-sections functor. -/
lemma coordinateHom_mul (g h : G) :
    coordinateHom ρ (g * h) = (coordinateHom ρ g).comp (coordinateHom ρ h) := by
  simp [coordinateHom, Aut.Aut_mul_def]

/-- The induced action on the ring of global sections. -/
@[instance_reducible]
def coordinateAction : MulSemiringAction G Γ(X, ⊤) :=
  MulSemiringAction.compHom _
    ({ toFun := coordinateHom ρ
       map_one' := coordinateHom_one ρ
       map_mul' := coordinateHom_mul ρ } : G →* (Γ(X, ⊤) →+* Γ(X, ⊤)))

/-- Scalar action computes by the genuine scheme pullback. -/
lemma coordinateAction_smul (g : G) (a : Γ(X, ⊤)) :
    let _ := coordinateAction ρ
    g • a = ((ρ g⁻¹).hom.appTop).hom a := rfl

/-- Equivariant morphisms give commuting coordinate maps. -/
lemma coordinateHom_comp (τ : G →* Aut Y) (f : X ⟶ Y)
    (hf : ∀ g : G, (ρ g).hom ≫ f = f ≫ (τ g).hom) (g : G) :
    (coordinateHom ρ g).comp f.appTop.hom =
      f.appTop.hom.comp (coordinateHom τ g) := by
  have h := congrArg (fun k : X ⟶ Y ↦ k.appTop.hom) (hf g⁻¹)
  exact h

/-- The canonical map to the spectrum of global sections respects the original action. -/
lemma toSpecΓ_equivariant (g : G) :
    (ρ g).hom ≫ X.toSpecΓ = X.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (coordinateHom ρ g⁻¹)) := by
  simpa only [coordinateHom, inv_inv, CommRingCat.ofHom_hom] using
    Scheme.toSpecΓ_naturality (ρ g).hom

end FLT.Mazur.SchemeCoordinateAction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineClosedBoundaryKernelLifting
public import FLT.Mazur.SchemeFiniteGroupSimultaneousInvariants

/-!
# Extending a correction while keeping the prescribed ambient input

First lift the stage correction to the ambient boundary kernel. A single
trace-one replacement then preserves both its invariant stage difference and
the original invariant boundary value. Subtracting from the supplied ambient
input gives the required correction, without changing that input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type u} [Group G] [Finite G] {Y X B : Scheme.{u}} [IsAffine Y]
  (τ : G →* Aut Y)
  (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y) (g : G),
    a ≫ (τ g).hom = a → g = 1)
  (ρ : G →* Aut X) (f : X ⟶ Y) [IsClosedImmersion f]
  (hf : ∀ g : G, (ρ g).hom ≫ f = f ≫ (τ g).hom)
  (β : G →* Aut B) (i : B ⟶ Y) [IsClosedImmersion i]
  (hi : ∀ g : G, (β g).hom ≫ i = i ≫ (τ g).hom)

include hfree hf hi in
/-- A prescribed finite-stage correction extends for the same prescribed ambient input. -/
theorem exists_prescribed_boundary_correction
    (t : invariantCoordinates β) (a : Γ(Y, ⊤)) (ha : i.appTop a = t.val)
    (z : Γ(X, ⊤)) (hz : (pullback.fst f i).appTop z = 0)
    (v : invariantCoordinates ρ) (hv : f.appTop a - z = v.val) :
    ∃ z' : Γ(Y, ⊤), i.appTop z' = 0 ∧ f.appTop z' = z ∧
      ∃ v' : invariantCoordinates τ, a - z' = v'.val := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ : IsAffine B := isAffine_of_isAffineHom i
  obtain ⟨z₀, hz₀, he₀⟩ :=
    AffineClosedBoundaryKernelLifting.exists_boundary_zero_lift f i z hz
  obtain ⟨v', hpres⟩ := exists_invariant_preserving_restrictions τ hfree (a - z₀)
  have hb : i.appTop v'.val = t.val := congrArg Subtype.val
    (hpres B β i hi t (by rw [map_sub, ha, hz₀, sub_zero]))
  have he : f.appTop v'.val = v.val := congrArg Subtype.val
    (hpres X ρ f hf v (by rw [map_sub, he₀]; exact hv))
  refine ⟨a - v'.val, ?_, ?_, v', ?_⟩
  · rw [map_sub, ha, hb, sub_self]
  · rw [map_sub, he, ← hv]
    ring
  · ring

end FLT.Mazur.SchemeFiniteGroupQuotient

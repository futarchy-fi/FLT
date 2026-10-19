/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupFreeBoundary

/-!
# Simultaneous invariant interpolation for a free action

A single trace-one weight makes an ambient coefficient invariant while preserving
every equivariant restriction that was already invariant. The restrictions can
have different targets and need not be surjective. No group order is inverted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction
namespace FLT.Mazur.SchemeFiniteGroupQuotient
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type u} [Group G] [Finite G] {Y : Scheme.{u}} [IsAffine Y]
  (τ : G →* Aut Y)
  (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y) (g : G),
    a ≫ (τ g).hom = a → g = 1)

include hfree in
/-- One invariant replacement preserves all already invariant equivariant restrictions. -/
theorem exists_invariant_preserving_restrictions (b : Γ(Y, ⊤)) :
    ∃ v : invariantCoordinates τ,
      ∀ (X : Scheme.{u}) (ρ : G →* Aut X) (f : X ⟶ Y)
        (hf : ∀ g : G, (ρ g).hom ≫ f = f ≫ (τ g).hom)
        (t : invariantCoordinates ρ), f.appTop b = t.val →
          invariantMap ρ τ f hf v = t := by
  let _ := Fintype.ofFinite G
  let _ := coordinateAction τ
  obtain ⟨a, ha⟩ := FiniteGroupQuotient.exists_orbitTrace_one G
    (coordinate_fixedPointIdeal_eq_top τ hfree)
  refine ⟨FiniteGroupQuotient.orbitTrace G (a * b), ?_⟩
  intro X ρ f hf t ht
  let _ := coordinateAction ρ
  have he : ∀ (g : G) x, f.appTop.hom (g • x) = g • f.appTop.hom x := by
    intro g x
    exact (congrArg (fun k : Γ(Y, ⊤) →+* Γ(X, ⊤) ↦ k x)
      (coordinateHom_comp ρ τ f hf g)).symm
  have h := FiniteGroupQuotient.boundaryMap_weightedTrace G f.appTop.hom he t b ht a
  rw [ha, map_one, one_mul] at h
  exact h

end FLT.Mazur.SchemeFiniteGroupQuotient

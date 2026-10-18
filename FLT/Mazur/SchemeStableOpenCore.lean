/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteOrbitOpenCore
public import FLT.Mazur.FiniteGroupOpenRestriction

/-!
# Stable cores retaining whole invariant fibers

Intersect all translates of an open with finite orbit. This produces the
largest stable subopen, and it retains every fiber of an invariant map
that was wholly contained in the original open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteOrbitOpenCore
variable {G : Type} [Group G] {X : Scheme} (ρ : G →* Aut X)
  (U : X.Opens)
  (hf : (Set.range (fun g : G ↦ (ρ g).hom ⁻¹' (U : Set X))).Finite)

/-- The constructed stable core lies in its original open. -/
theorem invariantOpen_le : invariantOpen ρ U hf ≤ U := by
  intro x hx
  have h := (mem_invariantOpen ρ U hf x).mp hx 1
  rw [map_one] at h
  exact h

/-- The finite-orbit core is stable as an actual scheme open. -/
theorem invariantOpen_stable (g : G) :
    (ρ g).hom ⁻¹ᵁ invariantOpen ρ U hf = invariantOpen ρ U hf := by
  let _ := pointAction ρ
  apply SetLike.coe_injective
  ext x
  exact FiniteOrbitOpenCore.smul_mem_core_iff (U : Set X) g x

/-- Every stable subopen of the original open factors through the core. -/
theorem le_invariantOpen (V : X.Opens)
    (hV : ∀ g : G, (ρ g).hom ⁻¹ᵁ V = V) (hVU : V ≤ U) :
    V ≤ invariantOpen ρ U hf := by
  intro x hx
  apply (mem_invariantOpen ρ U hf x).mpr
  intro g
  apply hVU
  change x ∈ (ρ g).hom ⁻¹ᵁ V
  rwa [hV g]

/-- Refinement to the core preserves an entire fiber of an invariant scheme map. -/
theorem fiber_subset_invariantOpen_iff {Y : Scheme} (f : X ⟶ Y)
    (hinv : ∀ g : G, (ρ g).hom ≫ f = f) (y : Y) :
    (∀ x : X, f x = y → x ∈ invariantOpen ρ U hf) ↔
      ∀ x : X, f x = y → x ∈ U := by
  constructor
  · intro h x hx
    exact invariantOpen_le ρ U hf (h x hx)
  · intro h x hx
    apply (mem_invariantOpen ρ U hf x).mpr
    intro g
    apply h
    have he := congrArg (fun a : X ⟶ Y ↦ a x) (hinv g)
    exact he.trans hx

/-- A finite acting group automatically gives the finite orbit needed for the construction. -/
theorem finite_open_orbit [Finite G] :
    (Set.range (fun g : G ↦ (ρ g).hom ⁻¹' (U : Set X))).Finite := Set.finite_range _

end FLT.Mazur.SchemeFiniteOrbitOpenCore

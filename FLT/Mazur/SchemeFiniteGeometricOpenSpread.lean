/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteGeometricAffine

/-!
# Simultaneous original open conditions near a geometric test

Intersect the inverse images of finitely many actual open immersions, then
choose one affine open containing the geometric test. All original maps lift
on that entire open, with their exact scheme morphism identities preserved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeFiniteGeometricOpenSpread
set_option backward.isDefEq.respectTransparency false
universe u
variable {Y : Scheme.{u}} {K : Type u} [Field K]

/-- Finitely many geometric incidences extend to actual maps on a common affine open. -/
theorem exists_lifts {ι : Type u} [Finite ι] (X Z : ι → Scheme.{u})
    (k : ∀ i, Z i ⟶ X i) [∀ i, IsOpenImmersion (k i)] (r : ∀ i, Y ⟶ X i)
    (b : Spec (.of K) ⟶ Y) (hb : ∀ i, r i (b default) ∈ Set.range (k i)) :
    ∃ (U : Scheme.{u}) (q : U ⟶ Y) (z : Spec (.of K) ⟶ U) (a : ∀ i, U ⟶ Z i),
      IsAffine U ∧ IsOpenImmersion q ∧ z ≫ q = b ∧
        (∀ i, a i ≫ k i = q ≫ r i) := by
  let W : Y.Opens := ⨅ i, (r i) ⁻¹ᵁ (k i).opensRange
  have hW : b default ∈ W := by
    change b default ∈ (W : Set Y)
    dsimp only [W]
    rw [Opens.coe_iInf, Set.mem_iInter]
    exact hb
  obtain ⟨U, q, z, hU, hq, hz, hr⟩ :=
    EtaleFiniteGeometricDiagram.exists_affine_factor b W hW
  have hi (i : ι) : Set.range (q ≫ r i) ⊆ Set.range (k i) := by
    rintro _ ⟨x, rfl⟩
    have hx : q x ∈ (W : Set Y) := hr ⟨x, rfl⟩
    dsimp only [W] at hx
    rw [Opens.coe_iInf, Set.mem_iInter] at hx
    exact hx i
  exact ⟨U, q, z, fun i ↦ IsOpenImmersion.lift (k i) (q ≫ r i) (hi i),
    hU, hq, hz, fun i ↦ IsOpenImmersion.lift_fac _ _ _⟩

/-- These neighborhood lifts recover any given geometric lifts as whole scheme morphisms. -/
theorem recover {U X Z : Scheme.{u}} (k : Z ⟶ X) [IsOpenImmersion k]
    (q : U ⟶ Y) (z : Spec (.of K) ⟶ U) (b : Spec (.of K) ⟶ Y)
    (r : Y ⟶ X) (a : U ⟶ Z) (g : Spec (.of K) ⟶ Z)
    (hz : z ≫ q = b) (ha : a ≫ k = q ≫ r) (hg : g ≫ k = b ≫ r) :
    z ≫ a = g := by
  apply (cancel_mono k).mp
  rw [Category.assoc, ha, ← Category.assoc, hz, hg]

end FLT.Mazur.SchemeFiniteGeometricOpenSpread

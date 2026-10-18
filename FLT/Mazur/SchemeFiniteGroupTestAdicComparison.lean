/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineUniformIdealPowers
public import FLT.Mazur.SchemeFiniteGroupFiniteFiberTests
public import FLT.Mazur.SchemeFiniteGroupInvariantPrincipal

/-!
# Uniform comparison of invariant tests and original closed-support equations

The fixed invariant tests and the original vanishing ideal define cofinal
ideal-power neighborhoods. The comparison constants are chosen on the original
Noetherian chart, before arbitrary, possibly nonreduced, coefficient changes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open Scheme.IdealSheafData
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}} [IsAffine X]
  [TopologicalSpace.NoetherianSpace X] (ρ : G →* Aut X) (Z : Set X) (hZ : IsClosed Z)
  (hstable : ∀ (g : G) (x : X), x ∈ Z → (ρ g).hom x ∈ Z)

/-- The fixed invariant equations, as an actual ideal sheaf on the original chart. -/
def orbitTestChartIdeal : X.IdealSheafData :=
  ofIdealTop (Ideal.span ((fun t : invariantCoordinates ρ ↦ t.val) ''
    (closedOrbitTests ρ Z hZ : Set (invariantCoordinates ρ))))

include hstable in
/-- The original test ideal has precisely the original stable closed support. -/
theorem orbitTestChartIdeal_support :
    (orbitTestChartIdeal ρ Z hZ).support = ⟨Z, hZ⟩ := by
  ext x
  change x ∈ X.zeroLocus (U := ⊤)
    ((Ideal.span ((fun t : invariantCoordinates ρ ↦ t.val) ''
      (closedOrbitTests ρ Z hZ : Set _)) : Ideal Γ(X, ⊤)) : Set _) ↔ x ∈ Z
  rw [Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  conv_rhs => rw [← closedOrbitImage_preimage ρ Z hZ hstable]
  change (∀ t ∈ _, x ∉ X.basicOpen t) ↔ quotientMap ρ x ∈ closedOrbitImage ρ Z hZ
  rw [mem_closedOrbitImage_iff_tests]
  constructor
  · intro h t ht
    have hx := h t.val ⟨t, ht, rfl⟩
    rw [← quotientMap_preimage_basicOpen ρ t] at hx
    exact not_not.mp hx
  · rintro h _ ⟨t, ht, rfl⟩
    rw [← quotientMap_preimage_basicOpen ρ t]
    exact fun hn ↦ hn (h t ht)

variable [IsNoetherian X]

include hstable in
/-- Original invariant tests and support equations have uniform orders on every coefficient base. -/
theorem orbitTestChart_uniform_comparison :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (k : ℕ),
        (vanishingIdeal ⟨Z, hZ⟩).comap f ^ (c * k) ≤
          (orbitTestChartIdeal ρ Z hZ).comap f ^ k ∧
        (orbitTestChartIdeal ρ Z hZ).comap f ^ (d * k) ≤
          (vanishingIdeal ⟨Z, hZ⟩).comap f ^ k := by
  apply AffineUniformIdealPowers.exists_uniform_comap_comparison
  rw [orbitTestChartIdeal_support ρ Z hZ hstable]
  rfl

end FLT.Mazur.SchemeFiniteGroupQuotient

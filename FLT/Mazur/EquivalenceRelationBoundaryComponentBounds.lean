/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRankFiltration
public import FLT.Mazur.AffineBoundaryComponentSpecialization
public import FLT.Mazur.EquivalenceRelationBoundaryRankRecovery

/-!
# Original rank bounds from the full product's minimal components

The original rank is a well-defined integer at every product point. It can
only decrease under specialization. Consequently its bounds are detected on
minimal components, without reducing the product or changing its coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "π" => chartBoundaryProduct n o U e hU s κ
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local instance componentBoundOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance componentBoundOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance componentBoundOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

/-- The unique original rank of a full scalar-product point. -/
def boundaryPointRank (z : boundaryProduct s κ) : ℕ :=
  (existsUnique_boundaryExactRank n o U e hU s κ z).exists.choose

/-- The chosen integer is the actual rank of every original chart lift. -/
theorem boundaryPointRank_spec (z : boundaryProduct s κ) :
    z ∈ boundaryExactRank n o U e hU s κ (boundaryPointRank n o U e hU s κ z) :=
  (existsUnique_boundaryExactRank n o U e hU s κ z).exists.choose_spec

/-- The numerical rank is characterized by membership in the original exact-rank piece. -/
theorem boundaryPointRank_eq_iff (z : boundaryProduct s κ) (m : ℕ) :
    boundaryPointRank n o U e hU s κ z = m ↔ z ∈ boundaryExactRank n o U e hU s κ m := by
  constructor
  · intro h
    simpa only [h] using boundaryPointRank_spec n o U e hU s κ z
  · intro h
    exact (existsUnique_boundaryExactRank n o U e hU s κ z).unique
      (boundaryPointRank_spec n o U e hU s κ z) h

/-- Original rank opens are exactly the numerical lower bounds on this rank. -/
theorem mem_boundaryRankOpen_iff (z : boundaryProduct s κ) (m : ℕ) :
    z ∈ boundaryRankOpen n o U e hU s κ m ↔ m ≤ boundaryPointRank n o U e hU s κ z := by
  have hz := boundaryPointRank_spec n o U e hU s κ z
  constructor
  · intro hm
    by_contra h
    exact hz.2 (boundaryRankOpen_antitone n o U e hU s κ (Nat.lt_of_not_ge h) hm)
  · intro h
    exact boundaryRankOpen_antitone n o U e hU s κ h hz.1

/-- Specialization cannot create larger original frames on the scalar product. -/
theorem boundaryPointRank_specializes {x y : boundaryProduct s κ} (h : x ⤳ y) :
    boundaryPointRank n o U e hU s κ y ≤ boundaryPointRank n o U e hU s κ x := by
  apply (mem_boundaryRankOpen_iff n o U e hU s κ x _).mp
  exact h.mem_open (boundaryRankOpen n o U e hU s κ _).isOpen
    (boundaryPointRank_spec n o U e hU s κ y).1

/-- Every point has an actual minimal component whose original rank bounds its own. -/
theorem exists_boundary_component_rank_bound (z : boundaryProduct s κ) :
    ∃ Q : minimalPrimes Γ(boundaryProduct s κ, ⊤),
      boundaryComponentPoint s κ Q ⤳ z ∧
        boundaryPointRank n o U e hU s κ z ≤
          boundaryPointRank n o U e hU s κ (boundaryComponentPoint s κ Q) := by
  obtain ⟨Q, hQ⟩ := exists_boundaryComponentPoint_specializes s κ z
  exact ⟨Q, hQ, boundaryPointRank_specializes n o U e hU s κ hQ⟩

/-- All rank bounds on the original product are detected on its minimal components. -/
theorem boundary_rank_bound_iff_components (m : ℕ) :
    (∀ z : boundaryProduct s κ, boundaryPointRank n o U e hU s κ z ≤ m) ↔
      ∀ Q : minimalPrimes Γ(boundaryProduct s κ, ⊤),
        boundaryPointRank n o U e hU s κ (boundaryComponentPoint s κ Q) ≤ m := by
  constructor
  · exact fun h Q ↦ h _
  · intro h z
    obtain ⟨Q, _, hQ⟩ := exists_boundary_component_rank_bound n o U e hU s κ z
    exact hQ.trans (h Q)

/-- A component of matching rank has matching rank at every one of its specializations. -/
theorem boundary_component_matching_specialization
    (Q : minimalPrimes Γ(boundaryProduct s κ, ⊤)) (z : boundaryProduct s κ)
    (hQ : boundaryPointRank n o U e hU s κ (boundaryComponentPoint s κ Q) = n)
    (hz : boundaryComponentPoint s κ Q ⤳ z) :
    boundaryPointRank n o U e hU s κ z = n := by
  apply Nat.le_antisymm
  · simpa only [hQ] using boundaryPointRank_specializes n o U e hU s κ hz
  · exact boundaryExactRank_ge n o U e hU s κ _ z
      (boundaryPointRank_spec n o U e hU s κ z)

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU

/-- Matching numerical rank at every product prime detects the full test-ideal equation. -/
theorem boundary_nilpotent_iff_pointRank :
    IsNilpotent (boundaryTestIdeal s κ tests) ↔
      ∀ z : boundaryProduct s κ, boundaryPointRank n o U e hU s κ z = n := by
  rw [boundaryTestIdeal_nilpotent_iff_chart_exactRank]
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := chartBoundaryProduct_surjective n o U e hU s κ z
    apply (boundaryPointRank_eq_iff n o U e hU s κ _ n).mpr
    change x ∈ π ⁻¹' boundaryExactRank n o U e hU s κ n
    rw [boundaryExactRank_preimage]
    exact h (Set.mem_range_self x)
  · rintro h _ ⟨x, rfl⟩
    have hx := (boundaryPointRank_eq_iff n o U e hU s κ (π x) n).mp (h (π x))
    change x ∈ π ⁻¹' boundaryExactRank n o U e hU s κ n at hx
    rw [boundaryExactRank_preimage] at hx
    exact hx

/-- The remaining full-product equation is exactly equality of the computed component ranks. -/
theorem boundary_nilpotent_iff_component_ranks :
    IsNilpotent (boundaryTestIdeal s κ tests) ↔
      ∀ Q : minimalPrimes Γ(boundaryProduct s κ, ⊤),
        boundaryPointRank n o U e hU s κ (boundaryComponentPoint s κ Q) = n := by
  rw [boundary_nilpotent_iff_pointRank]
  constructor
  · exact fun h Q ↦ h _
  · intro h z
    obtain ⟨Q, hQ⟩ := exists_boundaryComponentPoint_specializes s κ z
    exact boundary_component_matching_specialization n o U e hU s κ Q z (h Q) hQ

end FLT.Mazur.EquivalenceRelationNormalizedFrames

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryScalarCeiling
public import FLT.Mazur.AffineBoundaryScalarLocalProduct

/-!
# Exact rank bounds on the whole original scalar localization

The component ceiling is exactly the least bound on all points of the full
scalar-localized product, with the retained frame size as baseline. A strict
excess is attained on that entire local scheme by an actual minimal component.
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
local instance scalarLocalRankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarLocalRankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarLocalRankOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable [TopologicalSpace.NoetherianSpace A]
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU s κ
local notation "center" => fun Q : minimalPrimes C ↦
  boundaryScalarProjection s κ (boundaryComponentPoint s κ Q)
local notation "ranks" => fun Q : minimalPrimes C ↦ rankOf (boundaryComponentPoint s κ Q)

local notation "ceiling" => boundaryScalarRankCeiling n o U e hU s κ
local notation "bounded" => boundary_component_ranks_bounded n o U e hU s κ

/-- Every original product point with generizing scalar center obeys the component ceiling. -/
theorem boundary_point_rank_le_scalarCeiling (P : PrimeSpectrum T)
    (z : boundaryProduct s κ) (hz : (boundaryScalarProjection s κ z).asIdeal ≤ P.asIdeal) :
    rankOf z ≤ ceiling P := by
  obtain ⟨Q, hQz, hr⟩ := exists_boundary_component_rank_bound n o U e hU s κ z
  have hc : (center Q).asIdeal ≤ (boundaryScalarProjection s κ z).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hQz.map (boundaryScalarProjection s κ).continuous)
  exact hr.trans (boundary_component_rank_le_scalarCeiling n o U e hU s κ P Q (hc.trans hz))

/-- Bounds hold on every point of the whole original scalar-localized coefficient scheme. -/
theorem boundaryScalarLocal_point_rank_bounds (P : PrimeSpectrum T)
    (x : boundaryScalarLocalProduct s κ P) :
    n ≤ rankOf (boundaryScalarLocalMap s κ P x) ∧
      rankOf (boundaryScalarLocalMap s κ P x) ≤ ceiling P := by
  refine ⟨boundaryExactRank_ge n o U e hU s κ _ _
    (boundaryPointRank_spec n o U e hU s κ _), ?_⟩
  apply boundary_point_rank_le_scalarCeiling n o U e hU s κ P
  have hx := Set.mem_range_self (f := boundaryScalarLocalMap s κ P) x
  rwa [boundaryScalarLocalMap_range] at hx

/-- Full scalar-local point bounds are equivalent to the computed component ceiling bound. -/
theorem boundaryScalarLocal_rank_bound_iff (P : PrimeSpectrum T) (N : ℕ) (hN : n ≤ N) :
    (∀ x : boundaryScalarLocalProduct s κ P, rankOf (boundaryScalarLocalMap s κ P x) ≤ N) ↔
      ceiling P ≤ N := by
  constructor
  · intro h
    apply ScalarComponentRank.minimal center ranks n bounded P N hN
    intro Q hQ
    obtain ⟨x, hx⟩ := boundaryScalarLocalMap_component_lift s κ P Q hQ
    simpa only [hx] using h x
  · exact fun h x ↦ (boundaryScalarLocal_point_rank_bounds n o U e hU s κ P x).2.trans h

/-- A strict maximal rank excess is attained inside the full original scalar localization. -/
theorem boundaryScalarLocal_maximum_attained (P : PrimeSpectrum T) (hP : n < ceiling P) :
    ∃ Q : minimalPrimes C, ∃ x : boundaryScalarLocalProduct s κ P,
      boundaryScalarLocalMap s κ P x = boundaryComponentPoint s κ Q ∧
        rankOf (boundaryScalarLocalMap s κ P x) = ceiling P := by
  obtain ⟨Q, hQ, hr, _⟩ := boundaryScalarRankCeiling_attained n o U e hU s κ P hP
  obtain ⟨x, hx⟩ := boundaryScalarLocalMap_component_lift s κ P Q hQ
  exact ⟨Q, x, hx, by simpa only [hx] using hr⟩

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU

/-- Matching rank on the entire scalar localization is precisely original scalar nilpotence. -/
theorem boundaryScalarLocal_matching_iff (P : PrimeSpectrum T) :
    (∀ x : boundaryScalarLocalProduct s κ P, rankOf (boundaryScalarLocalMap s κ P x) = n) ↔
      P ∈ boundaryScalarNilpotenceOpen s κ tests := by
  rw [mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU s κ]
  constructor
  · intro h
    apply Nat.le_antisymm _ (boundaryScalarRankCeiling_ge n o U e hU s κ P)
    exact (boundaryScalarLocal_rank_bound_iff n o U e hU s κ P n le_rfl).mp
      (fun x ↦ (h x).le)
  · intro h x
    exact Nat.le_antisymm
      ((boundaryScalarLocal_point_rank_bounds n o U e hU s κ P x).2.trans h.le)
      (boundaryScalarLocal_point_rank_bounds n o U e hU s κ P x).1

end FLT.Mazur.EquivalenceRelationNormalizedFrames

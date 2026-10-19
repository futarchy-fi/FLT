/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationScalarLocalStages
public import FLT.Mazur.RelativeRankStageFaithfulDetection

/-!
# Detection by all bounded stages on the original scalar local product

Every locally Noetherian test of the full original scalar localization detects
coefficient equality from all orders of ranks n through the computed ceiling.
The finite flat chart transports detection faithfully. No original prime or
nilpotent is discarded, and Noetherianity of the scalar product is not inferred.
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
local instance scalarLocalDetectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarLocalDetectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarLocalDetectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable (P : PrimeSpectrum T)
local notation "l" => boundaryScalarLocalMap s κ P
local notation "localProduct" => boundaryScalarLocalProduct s κ P

local notation "δ" => boundaryScalarLocalProjection n o U e hU s κ P
local notation "endpoint" => boundaryScalarLocalEndpoint n o U e hU s κ P
local notation "rankOf" => boundaryPointRank n o U e hU s κ
variable [AlgebraicGeometry.IsNoetherian A]
local notation "ceiling" => boundaryScalarRankCeiling n o U e hU s κ P

/-- Every point of the full faithful local chart has rank in the computed interval. -/
theorem boundaryScalarLocal_rank_interval
    (x : boundaryScalarLocalChart n o U e hU s κ P) :
    ∃ m ∈ Set.Icc n ceiling, endpoint x ∈ exactRank (Over.mk p) m := by
  let m := rankOf (l (δ x))
  refine ⟨m, boundaryScalarLocal_point_rank_bounds n o U e hU s κ P (δ x), ?_⟩
  exact (boundaryScalarLocalEndpoint_rank_iff n o U e hU s κ P x m).mpr rfl

/-- Bounded original stages detect sections on every locally Noetherian scalar-local test. -/
theorem boundaryScalarLocal_test_zero {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (v : Y ⟶ localProduct) (a : Γ(localProduct, ⊤))
    (ha : ∀ m : ℕ, n ≤ m → m ≤ ceiling → ∀ k : ℕ,
      (boundaryScalarLocalRankMap n o U e hU s κ P m k).appTop a = 0) :
    v.appTop a = 0 := by
  apply test_zero_of_faithful_rank_stages (Over.mk p) endpoint δ (Set.Icc n ceiling)
    (boundaryScalarLocal_rank_interval n o U e hU s κ P) v a
  intro m hm k
  exact ha m hm.1 hm.2 k

/-- Every such test detects equality of the full coefficients, including nilpotents. -/
theorem boundaryScalarLocal_test_eq {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (v : Y ⟶ localProduct) (a c : Γ(localProduct, ⊤))
    (hac : ∀ m : ℕ, n ≤ m → m ≤ ceiling → ∀ k : ℕ,
      (boundaryScalarLocalRankMap n o U e hU s κ P m k).appTop a =
        (boundaryScalarLocalRankMap n o U e hU s κ P m k).appTop c) :
    v.appTop a = v.appTop c := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply boundaryScalarLocal_test_zero n o U e hU s κ P v (a - c)
  intro m hn hm k
  rw [map_sub, hac m hn hm k, sub_self]

/-- A nonzero tested coefficient is witnessed at a finite order of a bounded original rank. -/
theorem boundaryScalarLocal_nonzero_stage {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (v : Y ⟶ localProduct) (a : Γ(localProduct, ⊤)) (ha : v.appTop a ≠ 0) :
    ∃ m : ℕ, n ≤ m ∧ m ≤ ceiling ∧ ∃ k : ℕ,
      (boundaryScalarLocalRankMap n o U e hU s κ P m k).appTop a ≠ 0 := by
  by_contra h
  push Not at h
  exact ha (boundaryScalarLocal_test_zero n o U e hU s κ P v a h)

/-- Identity testing detects original coefficients if their actual scheme is locally Noetherian. -/
theorem boundaryScalarLocal_section_zero [IsLocallyNoetherian localProduct]
    (a : Γ(localProduct, ⊤))
    (ha : ∀ m : ℕ, n ≤ m → m ≤ ceiling → ∀ k : ℕ,
      (boundaryScalarLocalRankMap n o U e hU s κ P m k).appTop a = 0) : a = 0 := by
  simpa using boundaryScalarLocal_test_zero n o U e hU s κ P (𝟙 localProduct) a ha

end FLT.Mazur.EquivalenceRelationNormalizedFrames

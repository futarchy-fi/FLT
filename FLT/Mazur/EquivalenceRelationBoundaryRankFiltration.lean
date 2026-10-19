/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationQuotientRankOpens
public import FLT.Mazur.EquivalenceRelationBoundaryRankDescent

/-!
# Rank filtration on the entire original scalar product

Descended rank opens give locally closed, disjoint pieces on the full product.
Every original prime is in exactly one piece. The image of each old chart rank
stage is precisely that piece, so no component is hidden by a choice of lift.
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
local instance filtrationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance filtrationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance filtrationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

/-- Rank opens on the full original scalar product, with its unchanged structure sheaf. -/
def boundaryRankOpen (m : ℕ) : (boundaryProduct s κ).Opens :=
  boundaryProjection s κ ⁻¹ᵁ quotientRankOpen n o U e hU m

/-- The rank filtration agrees with the original endpoint on the whole faithful chart. -/
theorem boundaryRankOpen_preimage (m : ℕ) :
    π ⁻¹ᵁ boundaryRankOpen n o U e hU s κ m = b ⁻¹ᵁ rankImageOpen (Over.mk p) m := by
  unfold boundaryRankOpen chartBoundaryProduct chartBoundaryEndpoint chartBoundaryChart
  rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage,
    quotientRankOpen_preimage]
  rfl

/-- Higher rank opens are contained in all lower rank opens on the full product. -/
theorem boundaryRankOpen_antitone : Antitone (boundaryRankOpen n o U e hU s κ) := by
  intro aa bb hab z hz
  exact quotientRankOpen_antitone n o U e hU hab hz

/-- Exact rank on the product is defined by two consecutive original quotient opens. -/
def boundaryExactRank (m : ℕ) : Set (boundaryProduct s κ) :=
  (boundaryRankOpen n o U e hU s κ m : Set _) ∩
    (boundaryRankOpen n o U e hU s κ (m + 1) : Set _)ᶜ

/-- All lifts of a product point have the same exact original rank. -/
theorem boundaryExactRank_preimage (m : ℕ) :
    π ⁻¹' boundaryExactRank n o U e hU s κ m = b ⁻¹' exactRank (Over.mk p) m := by
  have h (l : ℕ) := congrArg (fun V : (chartBoundary n o U e hU s κ).Opens ↦
    (V : Set (chartBoundary n o U e hU s κ))) (boundaryRankOpen_preimage n o U e hU s κ l)
  exact congrArg₂ (fun X Y : Set _ ↦ X ∩ Yᶜ) (h m) (h (m + 1))

/-- Every stage has exactly the corresponding full-product rank piece as its image. -/
theorem boundaryRankProductMap_range (k m : ℕ) :
    Set.range (boundaryRankProductMap n o U e hU s κ k m) =
      boundaryExactRank n o U e hU s κ m := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    have h := rankPullback_endpoint (Over.mk p) b m k y
    change rankPullbackMap (Over.mk p) b m k y ∈ b ⁻¹' exactRank (Over.mk p) m at h
    rw [← boundaryExactRank_preimage n o U e hU s κ m] at h
    exact h
  · intro hz
    obtain ⟨x, rfl⟩ := chartBoundaryProduct_surjective n o U e hU s κ z
    have hx : x ∈ Set.range (rankPullbackMap (Over.mk p) b m k) := by
      rw [rankPullbackMap_range, ← boundaryExactRank_preimage n o U e hU s κ m]
      exact hz
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, rfl⟩

/-- The descended exact rank pieces are locally closed on the full original product. -/
theorem boundaryExactRank_isLocallyClosed (m : ℕ) :
    IsLocallyClosed (boundaryExactRank n o U e hU s κ m) :=
  (boundaryRankOpen n o U e hU s κ m).isOpen.isLocallyClosed.inter
    (boundaryRankOpen n o U e hU s κ (m + 1)).isOpen.isClosed_compl.isLocallyClosed

/-- Every product prime has one and only one original rank, independent of all chart lifts. -/
theorem existsUnique_boundaryExactRank (z : boundaryProduct s κ) :
    ∃! m : ℕ, z ∈ boundaryExactRank n o U e hU s κ m := by
  obtain ⟨x, rfl⟩ := chartBoundaryProduct_surjective n o U e hU s κ z
  have h (m : ℕ) := Set.ext_iff.mp (boundaryExactRank_preimage n o U e hU s κ m) x
  obtain ⟨m, hm⟩ := exists_exactRank (Over.mk p) (b x)
  refine ⟨m, (h m).mpr hm, fun l hl ↦ ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (exactRank_disjoint (Over.mk p) hne) ((h l).mp hl) hm

/-- No product point has rank below the original retained frame size. -/
theorem boundaryExactRank_ge (m : ℕ) (z : boundaryProduct s κ)
    (hz : z ∈ boundaryExactRank n o U e hU s κ m) : n ≤ m := by
  rw [← boundaryRankProductMap_range n o U e hU s κ 0 m] at hz
  obtain ⟨y, _⟩ := hz
  by_contra h
  exact (boundary_rankThickening_empty_below n o U e hU s κ m 0
    (Nat.lt_of_not_ge h)).false y

end FLT.Mazur.EquivalenceRelationNormalizedFrames

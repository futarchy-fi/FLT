/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicQuotient
public import FLT.Mazur.FiniteNeighborhoodQuotientOverlap

/-!
# Finite affine charts on the actual characteristic quotients

The same finite source index used for smooth subgroup coverage now indexes
affine quotient charts. Each original chart is recovered by base change,
and the quotient of its original invariant intersection is its scheme overlap.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The finite affine cover of each actual normalized characteristic quotient. -/
def normalizedQuotientCover (b : Bool) : (normalizedQuotient n b).OpenCover :=
  FiniteGroupNeighborhoodCover.finiteQuotientCover (normalizedRelabelAction n b)
    (normalizedLocus_hasFiniteNeighborhoods n b)

/-- The quotient cover retains the finite source-chart index. -/
instance normalizedQuotientCoverFintype (b : Bool) :
    Fintype (normalizedQuotientCover n b).I₀ := by
  unfold normalizedQuotientCover
  infer_instance

/-- The quotient of the actual action on the selected original affine chart. -/
def invariantAffineQuotient (i : InvariantAffineIndex n) : Scheme :=
  SchemeFiniteGroupQuotient.quotient (invariantAffineAction n i)

/-- Every selected quotient chart is affine. -/
instance invariantAffineQuotient_isAffine (i : InvariantAffineIndex n) :
    IsAffine (invariantAffineQuotient n i) := by
  unfold invariantAffineQuotient SchemeFiniteGroupQuotient.quotient
  infer_instance

/-- The actual quotient map on the original selected affine chart. -/
def invariantAffineQuotientMap (i : InvariantAffineIndex n) :
    invariantAffineChart n i ⟶ invariantAffineQuotient n i :=
  SchemeFiniteGroupQuotient.quotientMap (invariantAffineAction n i)

/-- The quotient map of each selected original affine chart is integral. -/
instance invariantAffineQuotientMap_integral (i : InvariantAffineIndex n) :
    IsIntegralHom (invariantAffineQuotientMap n i) := by
  unfold invariantAffineQuotientMap
  infer_instance

/-- Each selected quotient chart is covered by its original parameter chart. -/
instance invariantAffineQuotientMap_surjective (i : InvariantAffineIndex n) :
    Surjective (invariantAffineQuotientMap n i) := by
  unfold invariantAffineQuotientMap
  infer_instance

/-- The selected affine quotient chart includes into its original characteristic quotient. -/
def invariantAffineQuotientInclusion (i : InvariantAffineIndex n) :
    invariantAffineQuotient n i ⟶ normalizedQuotient n i.1 :=
  (normalizedQuotientCover n i.1).f i.2

/-- The actual selected affine quotient inclusion is an open immersion. -/
instance invariantAffineQuotientInclusion_isOpenImmersion (i : InvariantAffineIndex n) :
    IsOpenImmersion (invariantAffineQuotientInclusion n i) := by
  unfold invariantAffineQuotientInclusion
  infer_instance

/-- The quotient cover is connected to the original normalized parameter map. -/
@[reassoc] theorem invariantAffineQuotientMap_inclusion (i : InvariantAffineIndex n) :
    invariantAffineQuotientMap n i ≫ invariantAffineQuotientInclusion n i =
      invariantAffineInclusion n i ≫ normalizedQuotientMap n i.1 :=
  FiniteGroupNeighborhoodCover.finiteQuotientInclusion_fac _ _ i.2

/-- The original selected affine source is the actual pullback of its quotient chart. -/
theorem invariantAffineQuotient_isPullback (i : InvariantAffineIndex n) :
    IsPullback (invariantAffineInclusion n i) (invariantAffineQuotientMap n i)
      (normalizedQuotientMap n i.1) (invariantAffineQuotientInclusion n i) :=
  FiniteGroupNeighborhoodCover.finiteQuotientInclusion_isPullback _ _ i.2

/-- The quotient of the original invariant intersection of two selected source charts. -/
def invariantAffineOverlapQuotient (b : Bool) (i j : (invariantAffineCover n b).I₀) : Scheme :=
  SchemeFiniteGroupQuotient.quotient (StableAffineQuotient.action (normalizedRelabelAction n b)
    (FiniteGroupNeighborhoodCover.finiteOverlapChart (normalizedRelabelAction n b)
      (normalizedLocus_hasFiniteNeighborhoods n b) i j))

/-- Actual quotient intersections agree with the scheme pullbacks of the selected charts. -/
def invariantAffineOverlapQuotientIso (b : Bool) (i j : (invariantAffineCover n b).I₀) :
    invariantAffineOverlapQuotient n b i j ≅
      pullback (invariantAffineQuotientInclusion n ⟨b, i⟩)
        (invariantAffineQuotientInclusion n ⟨b, j⟩) :=
  FiniteGroupNeighborhoodCover.finiteOverlapIso _ _ i j

/-- The finite selected quotient charts cover each full characteristic quotient. -/
theorem invariantAffineQuotient_covers (b : Bool) (x : normalizedQuotient n b) :
    ∃ i : (invariantAffineCover n b).I₀,
      x ∈ Set.range (invariantAffineQuotientInclusion n ⟨b, i⟩) :=
  (normalizedQuotientCover n b).exists_eq x

end FLT.Mazur.CyclicCharacteristicAtlas

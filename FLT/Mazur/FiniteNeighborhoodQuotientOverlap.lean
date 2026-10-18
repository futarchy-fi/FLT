/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteNeighborhoodQuotientCover

/-!
# Actual overlaps of the finite quotient cover

Intersect the original selected stable affine opens. The quotient of the
restricted intersection is the scheme pullback of their quotient inclusions,
with both projections given by the original equivariant inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient FLT.Mazur.StableAffineQuotient
namespace FLT.Mazur.FiniteGroupNeighborhoodCover
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {G : Type} [Group G] [Finite G] {X : Scheme} [X.IsSeparated] [CompactSpace X]
  (ρ : G →* Aut X) (hX : FiniteAffineNeighborhood.HasNeighborhoods X)
  (i j : (finiteCover ρ hX).I₀)

/-- The original selected intersection, with its actual restricted group action. -/
def finiteOverlapChart : StableAffineQuotient.Chart ρ :=
  intersection ρ (finiteStableChart ρ hX i) (finiteStableChart ρ hX j)

/-- The quotient of the actual intersection includes into the first quotient chart. -/
def finiteOverlapLeft : quotient (action ρ (finiteOverlapChart ρ hX i j)) ⟶
    quotient (finiteAction ρ hX i) :=
  inclusion ρ (U := finiteOverlapChart ρ hX i j) (V := finiteStableChart ρ hX i)
    (intersection_le_left ρ (finiteStableChart ρ hX i) (finiteStableChart ρ hX j))

/-- The quotient of the actual intersection includes into the second quotient chart. -/
def finiteOverlapRight : quotient (action ρ (finiteOverlapChart ρ hX i j)) ⟶
    quotient (finiteAction ρ hX j) :=
  inclusion ρ (U := finiteOverlapChart ρ hX i j) (V := finiteStableChart ρ hX j)
    (intersection_le_right ρ (finiteStableChart ρ hX i) (finiteStableChart ρ hX j))

/-- The first quotient overlap inclusion is an open immersion. -/
instance finiteOverlapLeft_isOpenImmersion : IsOpenImmersion (finiteOverlapLeft ρ hX i j) := by
  unfold finiteOverlapLeft
  infer_instance

/-- The second quotient overlap inclusion is an open immersion. -/
instance finiteOverlapRight_isOpenImmersion : IsOpenImmersion (finiteOverlapRight ρ hX i j) := by
  unfold finiteOverlapRight
  infer_instance

/-- The two actual quotient overlap inclusions agree in the glued scheme. -/
@[reassoc] theorem finiteOverlap_condition :
    finiteOverlapLeft ρ hX i j ≫ finiteQuotientInclusion ρ hX i =
      finiteOverlapRight ρ hX i j ≫ finiteQuotientInclusion ρ hX j := by
  change inclusion ρ _ ≫ chartMap ρ _ = inclusion ρ _ ≫ chartMap ρ _
  rw [inclusion_chartMap, inclusion_chartMap]

/-- The quotient of the actual intersection is the scheme intersection of quotient charts. -/
def finiteOverlapIso : quotient (action ρ (finiteOverlapChart ρ hX i j)) ≅
    pullback (finiteQuotientInclusion ρ hX i) (finiteQuotientInclusion ρ hX j) :=
  chartIntersectionIso ρ (finiteStableChart ρ hX i) (finiteStableChart ρ hX j)

/-- The first pullback projection recovers the actual first quotient inclusion. -/
@[reassoc] theorem finiteOverlapIso_hom_fst :
    (finiteOverlapIso ρ hX i j).hom ≫
      pullback.fst (finiteQuotientInclusion ρ hX i) (finiteQuotientInclusion ρ hX j) =
        finiteOverlapLeft ρ hX i j :=
  chartIntersectionIso_hom_fst ρ (finiteStableChart ρ hX i) (finiteStableChart ρ hX j)

/-- The second pullback projection recovers the actual second quotient inclusion. -/
@[reassoc] theorem finiteOverlapIso_hom_snd :
    (finiteOverlapIso ρ hX i j).hom ≫
      pullback.snd (finiteQuotientInclusion ρ hX i) (finiteQuotientInclusion ρ hX j) =
        finiteOverlapRight ρ hX i j :=
  chartIntersectionIso_hom_snd ρ (finiteStableChart ρ hX i) (finiteStableChart ρ hX j)

/-- The actual quotient intersection square satisfies the scheme pullback property. -/
theorem finiteOverlap_isPullback :
    IsPullback (finiteOverlapLeft ρ hX i j) (finiteOverlapRight ρ hX i j)
      (finiteQuotientInclusion ρ hX i) (finiteQuotientInclusion ρ hX j) := by
  rw [← finiteOverlapIso_hom_fst, ← finiteOverlapIso_hom_snd]
  exact (IsPullback.of_hasPullback _ _).of_iso
    (finiteOverlapIso ρ hX i j).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

end FLT.Mazur.FiniteGroupNeighborhoodCover

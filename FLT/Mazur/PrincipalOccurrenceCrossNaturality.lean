/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrencePatchNaturality
public import FLT.Mazur.PrincipalOccurrenceCrossChartIntersections

/-!
# Transitions of actual cross-chart intersections

The two patch transitions induce a map of their pullbacks. This map
commutes with both outer overlap arrows, and its square over the shared
overlap is cartesian.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalOccurrencePatchOpen
  FiniteRelationLocalization.transition

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  {x y : PrincipalOccurrenceStage dst a b f}


variable (hxy : x ≤ y) (hx : ∀ i k, Function.Bijective (x.hom i k))
  (hy : ∀ i k, Function.Bijective (y.hom i k))
  {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)

/-- Refinement on the cross-chart intersection, constructed from its two projections. -/
def principalOccurrenceCrossTransition :
    principalOccurrenceCross y hy p q ⟶ principalOccurrenceCross x hx p q :=
  pullback.lift
    (principalOccurrenceCrossLeft y hy p q ≫ principalOccurrencePatchTransition hxy hx hy p)
    (principalOccurrenceCrossRight y hy p q ≫ principalOccurrencePatchTransition hxy hx hy q)
    (by
      simp only [Category.assoc, principalOccurrencePatchTransition_fac]
      exact pullback.condition_assoc _)

/-- The transition commutes with its first patch projection. -/
@[reassoc (attr := simp)] theorem principalOccurrenceCrossTransition_fst :
    principalOccurrenceCrossTransition hxy hx hy p q ≫ principalOccurrenceCrossLeft x hx p q =
      principalOccurrenceCrossLeft y hy p q ≫ principalOccurrencePatchTransition hxy hx hy p :=
  pullback.lift_fst _ _ _

/-- The transition commutes with its second patch projection. -/
@[reassoc (attr := simp)] theorem principalOccurrenceCrossTransition_snd :
    principalOccurrenceCrossTransition hxy hx hy p q ≫ principalOccurrenceCrossRight x hx p q =
      principalOccurrenceCrossRight y hy p q ≫ principalOccurrencePatchTransition hxy hx hy q :=
  pullback.lift_snd _ _ _

/-- The full transition square over the literal shared overlap commutes. -/
@[reassoc (attr := simp)] theorem principalOccurrenceCrossTransition_open :
    principalOccurrenceCrossTransition hxy hx hy p q ≫ principalOccurrenceCrossOpen x hx p q =
      principalOccurrenceCrossOpen y hy p q ≫ principalOccurrenceOverlapTransition hxy j := by
  simp only [principalOccurrenceCrossOpen, principalOccurrenceCrossTransition_fst_assoc,
    principalOccurrencePatchTransition_fac, Category.assoc]

/-- The left outer overlap route is natural under refinement. -/
@[reassoc] theorem principalOccurrenceCrossTransition_left :
    principalOccurrenceCrossTransition hxy hx hy p q ≫
        principalOccurrenceCrossOuterLeft x hx p q =
      principalOccurrenceCrossOuterLeft y hy p q ≫
        principalOccurrenceOverlapTransition hxy (dst p.1.val.1 p.2) := by
  simp only [principalOccurrenceCrossOuterLeft, principalOccurrenceCrossTransition_fst_assoc,
    principalOccurrencePatchTransition_other, Category.assoc]

/-- The right outer overlap route is natural under refinement. -/
@[reassoc] theorem principalOccurrenceCrossTransition_right :
    principalOccurrenceCrossTransition hxy hx hy p q ≫
        principalOccurrenceCrossOuterRight x hx p q =
      principalOccurrenceCrossOuterRight y hy p q ≫
        principalOccurrenceOverlapTransition hxy (dst q.1.val.1 q.2) := by
  simp only [principalOccurrenceCrossOuterRight, principalOccurrenceCrossTransition_snd_assoc,
    principalOccurrencePatchTransition_other, Category.assoc]

/-- Cross-chart intersection images pull back exactly under overlap transitions. -/
theorem principalOccurrenceCross_preimage :
    principalOccurrenceOverlapTransition hxy j ⁻¹ᵁ
        (principalOccurrenceCrossOpen x hx p q).opensRange =
      (principalOccurrenceCrossOpen y hy p q).opensRange := by
  rw [principalOccurrenceCross_opensRange, principalOccurrenceCross_opensRange,
    Scheme.Hom.preimage_inf, principalOccurrencePatch_preimage hxy hx hy p,
    principalOccurrencePatch_preimage hxy hx hy q]

/-- The actual cross-chart transition square is a scheme pullback. -/
theorem principalOccurrenceCrossTransition_isPullback :
    IsPullback (principalOccurrenceCrossTransition hxy hx hy p q)
      (principalOccurrenceCrossOpen y hy p q) (principalOccurrenceCrossOpen x hx p q)
      (principalOccurrenceOverlapTransition hxy j) := by
  apply IsOpenImmersion.isPullback
  · exact (principalOccurrenceCrossTransition_open hxy hx hy p q).symm
  · exact principalOccurrenceCross_preimage hxy hx hy p q

end FLT.Mazur.FiniteTypeRelationModel

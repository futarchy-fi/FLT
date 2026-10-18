/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeRefinement
public import FLT.Mazur.EquivalenceRelationCompleteMixedCoefficients

/-!
# Original arrows between frames sharing a strict subframe

A common selected endpoint constructs an original arrow between the two larger
frames by composing one coordinate with the inverse of the other. On a complete
source chart this proves the actual kernel-pair equation for every invariant
section. Completeness is retained explicitly and is not inferred near a point.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient EquivalenceRelationFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J) (ι : J ↪ I)
  {T : Scheme.{0}} (u v : T ⟶ source p q I o)
  (h : u ≫ subframeMap e o o' ι = v ≫ subframeMap e o o' ι)

include h in
/-- Equality of selected subframes gives equality of their distinguished original endpoints. -/
theorem subframe_common_endpoint :
    u ≫ coordinate p q I o (ι o') ≫ q = v ≫ coordinate p q I o (ι o') ≫ q := by
  have ht := congrArg (fun g ↦ g ≫ first p q J o') h
  simpa only [Category.assoc, subframeMap_first] using ht

/-- The actual original relation arrow associated to a pair with a common selection. -/
def subframePairArrow : T ⟶ D :=
  compose e (u ≫ coordinate p q I o (ι o'))
    (v ≫ coordinate p q I o (ι o') ≫ e.s) (by
      simp only [Category.assoc, e.symmetry₁]
      exact subframe_common_endpoint e o o' ι u v h)

/-- The constructed arrow starts at the first original frame endpoint. -/
@[reassoc] theorem subframePairArrow_first :
    subframePairArrow e o o' ι u v h ≫ p = u ≫ first p q I o := by
  rw [subframePairArrow, compose_fst, Category.assoc, coordinate_first]

/-- The constructed arrow ends at the second original frame endpoint. -/
@[reassoc] theorem subframePairArrow_second :
    subframePairArrow e o o' ι u v h ≫ q = v ≫ first p q I o := by
  simp only [subframePairArrow, compose_snd, Category.assoc, e.symmetry₂, coordinate_first]

variable [Etale p]
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
  (hc : (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o)

include hc in
/-- Complete source invariants agree on arbitrary tests with the same selected subframe. -/
theorem completeOpen_invariant_subframe_pair
    (t : invariantCoordinates (restrictedAction (action e I o) U hU))
    (u v : T ⟶ U.toScheme)
    (h : u ≫ U.ι ≫ subframeMap e o o' ι = v ≫ U.ι ≫ subframeMap e o o' ι) :
    u.appTop t.val = v.appTop t.val := by
  have he : (u ≫ U.ι) ≫ subframeMap e o o' ι =
      (v ≫ U.ι) ≫ subframeMap e o o' ι := by simpa only [Category.assoc] using h
  exact completeOpen_invariant_test e I o U hU hc t u v
    (subframePairArrow e o o' ι (u ≫ U.ι) (v ≫ U.ι) he)
    (by rw [subframePairArrow_first, Category.assoc])
    (by rw [subframePairArrow_second, Category.assoc])

end FLT.Mazur.EquivalenceRelationNormalizedFrames

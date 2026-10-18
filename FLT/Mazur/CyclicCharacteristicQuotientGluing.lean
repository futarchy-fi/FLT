/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointQuotientCover

/-!
# Gluing and source recovery for the finite assembled quotient atlas

The actual finite affine quotient cover gives scheme gluing data satisfying
the pullback cocycle. Its gluing recovers the constructed single quotient.
Each selected original source chart is recovered by the actual quotient map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The original selected affine source chart inside the single normalized source. -/
def disjointAffineInclusion (i : InvariantAffineIndex n) :
    invariantAffineChart n i ⟶ normalizedDisjointSource n :=
  invariantAffineInclusion n i ≫ normalizedDisjointInclusion n i.1

/-- The original selected affine source inclusions remain open immersions. -/
instance disjointAffineInclusion_isOpenImmersion (i : InvariantAffineIndex n) :
    IsOpenImmersion (disjointAffineInclusion n i) := by
  unfold disjointAffineInclusion
  infer_instance

/-- The original chart action is the restriction of the single assembled relabeling action. -/
@[reassoc] theorem disjointAffineAction_inclusion (i : InvariantAffineIndex n)
    (g : RelabelGroup n) :
    (invariantAffineAction n i g).hom ≫ disjointAffineInclusion n i =
      disjointAffineInclusion n i ≫ (normalizedDisjointAction n g).hom := by
  unfold disjointAffineInclusion
  rw [invariantAffineAction_inclusion_assoc, Category.assoc,
    normalizedDisjointAction_inclusion]

/-- The quotient chart square is cartesian for the single assembled quotient map. -/
theorem disjointAffineQuotient_isPullback (i : InvariantAffineIndex n) :
    IsPullback (disjointAffineInclusion n i) (invariantAffineQuotientMap n i)
      (normalizedDisjointQuotientMap n) (disjointAffineQuotientInclusion n i) :=
  (invariantAffineQuotient_isPullback n i).paste_horiz
    (normalizedDisjointQuotientMap_isPullback n i.1)

/-- The selected affine quotient maps retain their exact original source inclusions. -/
@[reassoc] theorem disjointAffineQuotientMap_inclusion (i : InvariantAffineIndex n) :
    invariantAffineQuotientMap n i ≫ disjointAffineQuotientInclusion n i =
      disjointAffineInclusion n i ≫ normalizedDisjointQuotientMap n :=
  (disjointAffineQuotient_isPullback n i).w.symm

/-- Actual finite gluing data on the selected invariant-coordinate quotient charts. -/
def disjointQuotientGlueData : Scheme.GlueData := (disjointAffineQuotientCover n).gluedCover

/-- The finite quotient atlas satisfies the full triple-overlap scheme cocycle. -/
theorem disjointQuotientGlueData_cocycle (i j k : InvariantAffineIndex n) :
    (disjointQuotientGlueData n).t' i j k ≫ (disjointQuotientGlueData n).t' j k i ≫
      (disjointQuotientGlueData n).t' k i j = 𝟙 _ :=
  (disjointQuotientGlueData n).cocycle i j k

/-- Gluing the selected finite affine quotient atlas recovers the actual single quotient. -/
def disjointQuotientGluingIso :
    (disjointQuotientGlueData n).glued ≅ normalizedDisjointQuotient n :=
  asIso (disjointAffineQuotientCover n).fromGlued

/-- The gluing comparison preserves every original selected quotient-chart inclusion. -/
@[reassoc] theorem disjointQuotientGluingIso_chart (i : InvariantAffineIndex n) :
    (disjointQuotientGlueData n).ι i ≫ (disjointQuotientGluingIso n).hom =
      disjointAffineQuotientInclusion n i :=
  (disjointAffineQuotientCover n).ι_fromGlued i

/-- Distinct characteristic components have empty intersections in this disjoint quotient. -/
theorem disjointAffineQuotient_overlap_empty (i j : InvariantAffineIndex n) (h : i.1 ≠ j.1) :
    IsEmpty ↑(pullback (disjointAffineQuotientInclusion n i)
      (disjointAffineQuotientInclusion n j)) := by
  apply isEmpty_of_commSq_sigmaι_of_ne
    (g := normalizedQuotient n) (i := i.1) (j := j.1) (hij := h)
  exact ⟨show
    (pullback.fst _ _ ≫ invariantAffineQuotientInclusion n i) ≫
        normalizedDisjointQuotientInclusion n i.1 =
      (pullback.snd _ _ ≫ invariantAffineQuotientInclusion n j) ≫
        normalizedDisjointQuotientInclusion n j.1 from by
    simpa only [disjointAffineQuotientInclusion, Category.assoc] using
      pullback.condition (f := disjointAffineQuotientInclusion n i)
        (g := disjointAffineQuotientInclusion n j)⟩

end FLT.Mazur.CyclicCharacteristicAtlas

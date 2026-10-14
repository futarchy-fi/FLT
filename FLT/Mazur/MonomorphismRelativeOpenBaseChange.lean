/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismRelativeOpen
public import FLT.Mazur.MonomorphismOpenImageBaseChange
public import FLT.Mazur.SchemeWholeFiberOpenBaseChange

/-!
# Effective target opens under genuine flat refinement

Base change the entire kernel and then the entire original relation. The
intrinsic effective target open is exactly the inverse image of the original
one. This includes nonreduced targets and every original relation arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.MonomorphismRelativeOpen
variable {D K T D' K' T' : Scheme.{u}} (m : D ⟶ K) [Mono m] (q : K ⟶ T)
  (a : D' ⟶ D) (m' : D' ⟶ K') (b : K' ⟶ K) (q' : K' ⟶ T') (t : T' ⟶ T)
  (hD : IsPullback a m' m b) (hK : IsPullback b q' q t)

include hD hK in
/-- The full-relation effective open commutes with flat finite-presentation refinement. -/
theorem targetOpen_baseChange [Flat t] [LocallyOfFinitePresentation t] :
    targetOpen m' q' = t ⁻¹ᵁ targetOpen m q := by
  let _ : Flat b := MorphismProperty.of_isPullback hK.flip inferInstance
  let _ : LocallyOfFinitePresentation b :=
    MorphismProperty.of_isPullback hK.flip inferInstance
  unfold targetOpen
  rw [MonomorphismOpenImage.locus_baseChange m a m' b hD]
  exact SchemeWholeFiberOpen.locus_flat_baseChange q b q' t hK _

include hD hK in
/-- A genuine fppf cover detects coverage without losing any nilpotent structure. -/
theorem targetOpen_top_iff_baseChange [Flat t] [LocallyOfFinitePresentation t]
    [Surjective t] : targetOpen m' q' = ⊤ ↔ targetOpen m q = ⊤ := by
  let _ : Flat b := MorphismProperty.of_isPullback hK.flip inferInstance
  let _ : LocallyOfFinitePresentation b :=
    MorphismProperty.of_isPullback hK.flip inferInstance
  unfold targetOpen
  rw [MonomorphismOpenImage.locus_baseChange m a m' b hD]
  exact SchemeWholeFiberOpen.locus_top_iff_baseChange q b q' t hK _ t.isOpenMap

/-- The full kernel after arbitrary target refinement, with its original kernel coordinate. -/
abbrev refinedKernel (t : T' ⟶ T) : Scheme := pullback q t

/-- The full original relation after that same refinement. -/
abbrev refinedRelation (t : T' ⟶ T) : Scheme := pullback m (pullback.fst q t)

/-- The actual comparison on the refined whole kernel, not a selected relation branch. -/
abbrev refinedComparison (t : T' ⟶ T) :
    refinedRelation m q t ⟶ refinedKernel q t := pullback.snd m (pullback.fst q t)

/-- The concrete iterated pullback construction has exactly the pulled-back effective open. -/
theorem refined_targetOpen [Flat t] [LocallyOfFinitePresentation t] :
    targetOpen (refinedComparison m q t) (pullback.snd q t) =
      t ⁻¹ᵁ targetOpen m q :=
  targetOpen_baseChange m q (pullback.fst m (pullback.fst q t))
    (refinedComparison m q t) (pullback.fst q t) (pullback.snd q t) t
    (.of_hasPullback _ _) (.of_hasPullback _ _)

end FLT.Mazur.MonomorphismRelativeOpen

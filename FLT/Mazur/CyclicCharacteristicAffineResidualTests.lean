/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualSections
public import FLT.Mazur.CyclicCharacteristicResidualTransitionDescent

/-!
# Full residual comparisons on affine scheme tests

Every compatible comparison between affine-chart parameters factors through the
full restricted arrow scheme. Thus its residual invariants control arbitrary
scheme tests, retaining the infinitesimal comparison data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- An actual comparison whose endpoints lie in the affine chart restricts to its arrows. -/
def affineResidualTestArrow {T : Scheme} (p q : T ⟶ invariantAffineChart n i)
    (a : ProductArrow n (p ≫ invariantAffineInclusion n i)
      (q ≫ invariantAffineInclusion n i)) : T ⟶ (affineResidualDomain n i).toScheme :=
  IsOpenImmersion.lift (affineResidualDomain n i).ι a.val (by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨a.val x, ?_⟩, rfl⟩
    change productArrowSource n i.1 i.1 (a.val x) ∈
      Set.range (invariantAffineInclusion n i)
    exact ⟨p x, (congrArg (fun f => f x) (productArrow_source n i.1 i.1 a)).symm⟩)

/-- The restricted comparison has the original source parameter. -/
@[reassoc] theorem affineResidualTestArrow_source {T : Scheme}
    (p q : T ⟶ invariantAffineChart n i)
    (a : ProductArrow n (p ≫ invariantAffineInclusion n i)
      (q ≫ invariantAffineInclusion n i)) :
    affineResidualTestArrow n i p q a ≫ affineResidualSource n i = p := by
  apply (cancel_mono (invariantAffineInclusion n i)).mp
  rw [Category.assoc, affineResidualSource_inclusion, ← Category.assoc]
  rw [affineResidualTestArrow, IsOpenImmersion.lift_fac, productArrow_source]

/-- The restricted comparison has the original target parameter. -/
@[reassoc] theorem affineResidualTestArrow_target {T : Scheme}
    (p q : T ⟶ invariantAffineChart n i)
    (a : ProductArrow n (p ≫ invariantAffineInclusion n i)
      (q ≫ invariantAffineInclusion n i)) :
    affineResidualTestArrow n i p q a ≫ affineResidualTarget n i = q := by
  apply (cancel_mono (invariantAffineInclusion n i)).mp
  rw [Category.assoc, affineResidualTarget_inclusion, ← Category.assoc]
  rw [affineResidualTestArrow, IsOpenImmersion.lift_fac, productArrow_target]

/-- Full residual invariance controls all compatible original-family scheme tests. -/
theorem affineResidual_invariant_on_test {Y T : Scheme}
    (f : invariantAffineChart n i ⟶ Y)
    (hf : affineResidualSource n i ≫ f = affineResidualTarget n i ≫ f)
    (p q : T ⟶ invariantAffineChart n i)
    (h : UnmarkedRelated n i.1 i.1
      (p ≫ invariantAffineInclusion n i) (q ≫ invariantAffineInclusion n i)) :
    p ≫ f = q ≫ f := by
  obtain ⟨a⟩ := h
  let k := productCompatibleParameter n i.1 i.1 _ _ a
  have he := congrArg (affineResidualTestArrow n i p q k ≫ ·) hf
  simpa only [← Category.assoc, affineResidualTestArrow_source,
    affineResidualTestArrow_target] using he

end FLT.Mazur.CyclicCharacteristicOrbit

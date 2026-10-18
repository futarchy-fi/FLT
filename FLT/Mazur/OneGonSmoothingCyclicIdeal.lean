/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingFaithfulCyclicSubgroup

/-!
# The whole-curve ideal and generator of the smoothing's cyclic subgroup

The actual closed subgroup ideal is the product of all original section
ideals. Its component-one generator has order dividing n, and its powers
enumerate exactly those sections, including over singular fibers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R) (n : ℕ) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of R))
  (f : Over.mk g ⟶ relativeCyclicParameter t n)

/-- The actual whole-curve ideal of the rank-n subgroup on this smoothing test. -/
def relativeCyclicIdeal : ((Over.pullback g).obj (family t)).left.IdealSheafData :=
  (relativeCyclicCurveMap t n g f).left.ker

/-- Each subgroup component is exactly the original faithful cyclic section in the whole curve. -/
theorem relativeCyclicCurveMap_component (i : ZMod n) :
    ConstantCyclicGroup.component T n i ≫ relativeCyclicCurveMap t n g f =
      relativeCyclicMarking t n g f (.ofAdd i) ≫ relativeTestInclusion t g := by
  exact ConstantCyclicSectionMap.component_toScheme_assoc _ i _

/-- The entire closed subgroup has the original cyclic section product as its ideal. -/
theorem relativeCyclicIdeal_product :
    relativeCyclicIdeal t n g f = ∏ i : ZMod n,
      (relativeCyclicMarking t n g f (.ofAdd i) ≫ relativeTestInclusion t g).left.ker := by
  let _ := relativeTestFamily_proper t g
  have hd : UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦
      ConstantCyclicGroup.component T n i ≫ relativeCyclicCurveMap t n g f) := by
    intro V k hV i j hij
    apply relativeCyclicMarking_distinct t n g f V k hV
    have : Mono (relativeTestInclusion t g) := Over.mono_of_mono_left _
    apply (cancel_mono (relativeTestInclusion t g)).mp
    simpa only [relativeCyclicCurveMap_component, Category.assoc] using hij
  exact (ConstantCyclicRelativeClosed.kernel_eq_component_product _ hd).trans
    (by simp only [relativeCyclicCurveMap_component])

/-- The actual generator section of the rank-n subgroup. -/
def relativeCyclicGenerator : 𝟙_ (Over T) ⟶ ConstantCyclicGroup.model T n :=
  ConstantCyclicGroup.component T n 1

/-- The generator has the required cyclic torsion relation over the entire base. -/
theorem relativeCyclicGenerator_pow : (relativeCyclicGenerator (T := T) n) ^ n = 1 := by
  change ConstantCyclicGroup.component T n 1 ^ n = 1
  rw [← ConstantCyclicGenerator.component_natCast, ZMod.natCast_self,
    ConstantCyclicGenerator.component_zero]

/-- Its image in the full smoothing is the original marked generator. -/
theorem relativeCyclicGenerator_curve :
    relativeCyclicGenerator (T := T) n ≫ relativeCyclicCurveMap t n g f =
      relativeCyclicMarking t n g f (.ofAdd 1) ≫ relativeTestInclusion t g :=
  relativeCyclicCurveMap_component t n g f 1

/-- The scheme-theoretic ideal is exactly the full generator orbit, with all n factors. -/
theorem relativeCyclicIdeal_generator_product :
    relativeCyclicIdeal t n g f = ∏ i : Fin n,
      ((relativeCyclicGenerator (T := T) n ^ i.val) ≫
        relativeCyclicCurveMap t n g f).left.ker := by
  rw [relativeCyclicIdeal_product, ← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.prod_congr rfl
  intro i _
  rw [← relativeCyclicCurveMap_component]
  exact congrArg (fun s ↦ (s ≫ relativeCyclicCurveMap t n g f).left.ker)
    (ConstantCyclicGenerator.component_pow T n i)

end FLT.Mazur.OneGonSmoothing

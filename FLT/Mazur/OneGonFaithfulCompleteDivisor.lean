/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFaithfulCompleteSubgroup
public import FLT.Mazur.OneGonSmoothingCyclicCartier
public import FLT.Mazur.SectionSumFinite

/-!
# The actual cyclic Cartier divisor on the original complete cubic

The closed subgroup ideal equals the product of the constructed section
ideals. Smooth relative dimension one makes this divisor relative Cartier;
its closed subscheme is finite over the complete coefficient spectrum.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))

/-- The actual full-curve ideal of the constructed complete cyclic subgroup. -/
def faithfulCompleteIdeal : (family (t)).left.IdealSheafData :=
  (faithfulCompleteCurveMap K n labels hlabels).left.ker

/-- All original cyclic labels occur in the actual scheme-theoretic divisor ideal. -/
theorem faithfulCompleteIdeal_product :
    faithfulCompleteIdeal K n labels hlabels = ∏ i : ZMod n,
      (faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫
        relativeGroupInclusion (t)).left.ker := by
  let _ := family_proper (t)
  exact (ConstantCyclicRelativeClosed.kernel_eq_component_product _
    (faithfulCompleteCurveMap_distinct K n labels hlabels)).trans
      (by simp only [faithfulCompleteCurveMap_component])

/-- The entire cyclic subgroup is relative Cartier in the original complete curve. -/
theorem faithfulCompleteIdeal_cartier :
    RelativeEffectiveCartier (family (t)).hom (faithfulCompleteIdeal K n labels hlabels) := by
  let _ := family_proper (t)
  have : SmoothOfRelativeDimension 1
      ((relativeGroupInclusion (t)).left ≫ (family (t)).hom) := by
    rw [(relativeGroupInclusion (t)).w]
    exact relativeGroup_dimension (t)
  rw [faithfulCompleteIdeal_product]
  exact relativeEffectiveCartier_smoothOpen_section_prod (relativeGroupInclusion (t)).left
    (family (t)).hom Finset.univ
    (fun i : ZMod n ↦ (faithfulCompleteMarking K n labels hlabels (.ofAdd i)).left)
    (fun i _ ↦ (faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫
      relativeGroupInclusion (t)).w)

/-- The actual closed divisor subscheme is finite over the original complete base. -/
theorem faithfulCompleteIdeal_finite :
    IsFinite ((faithfulCompleteIdeal K n labels hlabels).subschemeι ≫ (family (t)).hom) := by
  let _ := family_proper (t)
  rw [faithfulCompleteIdeal_product]
  exact isFinite_section_prod _ Finset.univ
    (fun i : ZMod n ↦ (faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫
      relativeGroupInclusion (t)).left)
    (fun i _ ↦ (faithfulCompleteMarking K n labels hlabels (.ofAdd i) ≫
      relativeGroupInclusion (t)).w)

/-- The subgroup retains its original rank, independently of its embedding in the curve. -/
theorem faithfulCompleteSubgroup_degree :
    FiniteLocallyFreeDegree (ConstantCyclicGroup.model S n).hom n :=
  ConstantCyclicRelativeGeometry.degree S n

/-- The component-one section generates exactly the full divisor ideal. -/
theorem faithfulCompleteIdeal_generator_product :
    faithfulCompleteIdeal K n labels hlabels = ∏ i : Fin n,
      ((relativeCyclicGenerator (T := S) n ^ i.val) ≫
        faithfulCompleteCurveMap K n labels hlabels).left.ker := by
  rw [faithfulCompleteIdeal_product, ← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.prod_congr rfl
  intro i _
  rw [← faithfulCompleteCurveMap_component]
  exact congrArg (fun s ↦ (s ≫ faithfulCompleteCurveMap K n labels hlabels).left.ker)
    (ConstantCyclicGenerator.component_pow S n i)

end FLT.Mazur.OneGonSmoothing

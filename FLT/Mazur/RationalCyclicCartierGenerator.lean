/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RationalCyclicSubgroup
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup
public import FLT.Mazur.RelativeSums

/-!
# The actual Cartier generator of a rational cyclic subgroup

The closed subgroup kernel is the product of the distinct rational orbit
ideals. On a smooth relative curve each orbit section is Cartier, giving the
Cartier-generator condition for the prescribed component-one section.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve

variable {K : Type} [Field K] (E : GeneralizedEllipticCurve (Spec (.of K)))
  {n : ℕ} [NeZero n] (P : 𝟙_ (Over (Spec (.of K))) ⟶ E.group) (ho : orderOf P = n)

/-- The actual closed subgroup ideal is the product of the generator's orbit ideals. -/
theorem rationalCyclicSubgroup_ideal :
    (E.rationalCyclicSubgroup P ho).ideal = ∏ i : Fin n,
      ((E.rationalCyclicGenerator P ho ^ i.val) ≫
        (E.rationalCyclicSubgroup P ho).curveMap).left.ker := by
  have : IsProper E.curve.hom := E.family.family.1
  let H := E.rationalCyclicSubgroup P ho
  have : Mono E.inclusion := Over.mono_of_mono_left E.inclusion
  have hi : Function.Injective (fun i : ZMod n ↦
      ConstantCyclicGroup.component (Spec (.of K)) n i ≫ H.curveMap) := by
    intro i j h
    have hh : ExactOrderCyclicPowers.powersHom P ho (Multiplicative.ofAdd i) ≫ E.inclusion =
        ExactOrderCyclicPowers.powersHom P ho (Multiplicative.ofAdd j) ≫ E.inclusion := by
      simpa only [H, FiniteSubgroup.curveMap, rationalCyclicSubgroup, Category.assoc,
        ConstantCyclicSectionMap.component_toScheme_assoc] using h
    exact congrArg Multiplicative.toAdd
      (ExactOrderCyclicPowers.powersHom_injective P ho ((cancel_mono E.inclusion).mp hh))
  change H.curveMap.left.ker = _
  rw [ConstantCyclicSectionClosed.kernel_eq_component_product H.curveMap hi]
  rw [← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.prod_congr rfl
  intro i _
  have he : ConstantCyclicGroup.component (Spec (.of K)) n (ZMod.finEquiv n i) =
      E.rationalCyclicGenerator P ho ^ i.val :=
    ConstantCyclicGenerator.component_pow (Spec (.of K)) n i
  exact congrArg (fun s ↦ (s ≫ H.curveMap).left.ker) he

/-- On a smooth curve the original rational generator is an actual Cartier generator. -/
theorem rationalCyclicGenerator_isCartierGenerator [SmoothOfRelativeDimension 1 E.curve.hom] :
    (E.rationalCyclicSubgroup P ho).IsCartierGenerator (E.rationalCyclicGenerator P ho) := by
  have : IsProper E.curve.hom := E.family.family.1
  refine ⟨?_, ?_, E.rationalCyclicSubgroup_ideal P ho⟩
  · change ConstantCyclicGroup.component (Spec (.of K)) n 1 ^ n = 1
    rw [← ConstantCyclicGenerator.component_natCast, ZMod.natCast_self,
      ConstantCyclicGenerator.component_zero]
  · rw [E.rationalCyclicSubgroup_ideal P ho]
    exact FCurve.relativeEffectiveCartier_section_prod E.curve.hom Finset.univ
      (fun i : Fin n ↦ ((E.rationalCyclicGenerator P ho ^ i.val) ≫
        (E.rationalCyclicSubgroup P ho).curveMap).left) (fun i _ ↦ Over.w _)

end FLT.Mazur.GeneralizedEllipticCurve

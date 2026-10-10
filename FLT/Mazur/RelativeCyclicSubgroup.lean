/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicRelativeClosed
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup
public import FLT.Mazur.RelativeSums

/-!
# The finite subgroup and Cartier generator of a relative cyclic marking

A universally distinct cyclic marking constructs a finite etale closed subgroup
of rank n over an arbitrary base. On a smooth curve its component-one section is
an actual Cartier generator, with the full scheme-theoretic orbit ideal.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve

open UniversallyDistinctSections

variable {S : Scheme.{0}} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (Multiplicative.ofAdd i)))

/-- The marking's actual closed finite locally free subgroup. -/
def relativeCyclicSubgroup : E.FiniteSubgroup n := by
  have : IsProper E.curve.hom := E.family.family.1
  have : IsSeparated E.group.hom := by
    rw [← E.inclusion.w]
    infer_instance
  exact
    { carrier := ConstantCyclicGroup.model S n
      inclusion := ConstantCyclicSectionMap.toScheme φ
      closed := ConstantCyclicRelativeClosed.toScheme_closed φ hφ
      degree := ConstantCyclicRelativeGeometry.degree S n }

/-- The constructed subgroup is etale over its whole base. -/
theorem relativeCyclicSubgroup_etale : Etale (E.relativeCyclicSubgroup φ hφ).carrier.hom :=
  ConstantCyclicRelativeGeometry.etale S n

/-- The component-one section in the actual subgroup scheme. -/
def relativeCyclicGenerator : 𝟙_ (Over S) ⟶ (E.relativeCyclicSubgroup φ hφ).carrier :=
  ConstantCyclicGroup.component S n 1

/-- The subgroup generator retains the original marked point. -/
theorem relativeCyclicGenerator_inclusion :
    E.relativeCyclicGenerator φ hφ ≫ (E.relativeCyclicSubgroup φ hφ).inclusion =
      φ (Multiplicative.ofAdd 1) :=
  ConstantCyclicSectionMap.component_toScheme φ 1

/-- The whole-curve subgroup ideal is exactly the generator orbit product. -/
theorem relativeCyclicSubgroup_ideal :
    (E.relativeCyclicSubgroup φ hφ).ideal = ∏ i : Fin n,
      ((E.relativeCyclicGenerator φ hφ ^ i.val) ≫
        (E.relativeCyclicSubgroup φ hφ).curveMap).left.ker := by
  have : IsProper E.curve.hom := E.family.family.1
  let H := E.relativeCyclicSubgroup φ hφ
  have : Mono E.inclusion := Over.mono_of_mono_left E.inclusion
  have hi : UniversallyDistinct (fun i : ZMod n ↦
      ConstantCyclicGroup.component S n i ≫ H.curveMap) := by
    intro V g hV i j hij
    apply hφ V g hV
    apply (cancel_mono E.inclusion).mp
    simpa only [H, FiniteSubgroup.curveMap, relativeCyclicSubgroup, Category.assoc,
      ConstantCyclicSectionMap.component_toScheme_assoc] using hij
  change H.curveMap.left.ker = _
  rw [ConstantCyclicRelativeClosed.kernel_eq_component_product H.curveMap hi]
  rw [← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.prod_congr rfl
  intro i _
  have he : ConstantCyclicGroup.component S n (ZMod.finEquiv n i) =
      E.relativeCyclicGenerator φ hφ ^ i.val :=
    ConstantCyclicGenerator.component_pow S n i
  exact congrArg (fun s ↦ (s ≫ H.curveMap).left.ker) he

variable [SmoothOfRelativeDimension 1 E.curve.hom]

/-- Smoothness proves the Cartier-generator property of the constructed section. -/
theorem relativeCyclicGenerator_isCartierGenerator :
    (E.relativeCyclicSubgroup φ hφ).IsCartierGenerator (E.relativeCyclicGenerator φ hφ) := by
  have : IsProper E.curve.hom := E.family.family.1
  refine ⟨?_, ?_, E.relativeCyclicSubgroup_ideal φ hφ⟩
  · change ConstantCyclicGroup.component S n 1 ^ n = 1
    rw [← ConstantCyclicGenerator.component_natCast, ZMod.natCast_self,
      ConstantCyclicGenerator.component_zero]
  · rw [E.relativeCyclicSubgroup_ideal φ hφ]
    exact FCurve.relativeEffectiveCartier_section_prod E.curve.hom Finset.univ
      (fun i : Fin n ↦ ((E.relativeCyclicGenerator φ hφ ^ i.val) ≫
        (E.relativeCyclicSubgroup φ hφ).curveMap).left) (fun i _ ↦ Over.w _)

/-- The actual finite subgroup satisfies fppf-local cyclicity. -/
theorem relativeCyclicSubgroup_isCyclic : (E.relativeCyclicSubgroup φ hφ).IsCyclic :=
  (E.relativeCyclicGenerator_isCartierGenerator φ hφ).isCyclic _

/-- Its actual ideal defines a relative effective Cartier divisor. -/
theorem relativeCyclicSubgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier E.curve.hom (E.relativeCyclicSubgroup φ hφ).ideal :=
  (E.relativeCyclicGenerator_isCartierGenerator φ hφ).2.1

end FLT.Mazur.GeneralizedEllipticCurve

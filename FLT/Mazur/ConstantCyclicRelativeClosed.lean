/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicRelativeGeometry
public import FLT.Mazur.ConstantCyclicSectionMap
public import FLT.Mazur.UniversallyDistinctSections

/-!
# Closed cyclic markings over arbitrary schemes

A universally distinct family of cyclic sections embeds the actual constant
group as a closed subgroup. The kernel is the product of the component ideals,
without a rational-point or reduced-base hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.ConstantCyclicRelativeClosed

open ConstantCyclicRelativeGeometry UniversallyDistinctSections

variable {S : Scheme.{0}} {n : ℕ} [NeZero n] {X : Over S} [IsSeparated X.hom]
  (d : ConstantCyclicGroup.model S n ⟶ X)
  (hd : UniversallyDistinct (fun i : ZMod n ↦ ConstantCyclicGroup.component S n i ≫ d))

include hd

/-- A map whose components are universally distinct is a closed immersion. -/
theorem closed : IsClosedImmersion d.left := by
  have hc := UniversallyDistinctSections.closed _ hd
  rw [← underlying_components S n d] at hc
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsClosedImmersion)
    (underlyingIso S n).hom d.left).mp hc

/-- The subgroup kernel is the product of its actual section ideals. -/
theorem kernel_eq_component_product : d.left.ker = ∏ i : ZMod n,
    (ConstantCyclicGroup.component S n i ≫ d).left.ker := by
  rw [← Scheme.Hom.ker_comp_of_isIso (underlyingIso S n).hom d.left,
    underlying_components]
  exact (UniversallyDistinctSections.product_eq_kernel _ hd).symm

omit hd

variable {G : Over S} [GrpObj G] [IsSeparated G.hom]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ G))
  (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (Multiplicative.ofAdd i)))

include hφ

/-- Universal faithfulness supplies a closed immersion of actual group schemes. -/
theorem toScheme_closed : IsClosedImmersion (ConstantCyclicSectionMap.toScheme φ).left := by
  apply closed
  simpa only [ConstantCyclicSectionMap.component_toScheme] using hφ

/-- The group inclusion has the product of the given marking ideals. -/
theorem toScheme_kernel : (ConstantCyclicSectionMap.toScheme φ).left.ker =
    ∏ i : ZMod n, (φ (Multiplicative.ofAdd i)).left.ker := by
  have hd' : UniversallyDistinct (fun i : ZMod n ↦ ConstantCyclicGroup.component S n i ≫
      ConstantCyclicSectionMap.toScheme φ) := by
    simpa only [ConstantCyclicSectionMap.component_toScheme] using hφ
  simpa only [ConstantCyclicSectionMap.component_toScheme] using
    kernel_eq_component_product (ConstantCyclicSectionMap.toScheme φ) hd'

end FLT.Mazur.ConstantCyclicRelativeClosed

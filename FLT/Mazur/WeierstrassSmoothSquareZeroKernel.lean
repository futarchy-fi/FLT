/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothInfinitesimalAddition

/-!
# The square-zero reduction kernel of the full smooth group

The original X coordinate identifies the entire reduction kernel with the
additive square-zero ideal. This applies to singular Weierstrass fibers too.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (I : Ideal A) (hI : I ^ 2 = ⊥)

/-- Actual quotient restriction on the full smooth Weierstrass group. -/
def smoothSquareZeroReduction :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralSmoothGroup W).X) →*
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I)))) ⟶
      (integralSmoothGroup W).X) where
  toFun p := squareZeroQuotientTestMap I ≫ p
  map_one' := comp_one _
  map_mul' := comp_mul _

/-- Every point in the square-zero reduction kernel has an actual chart parameter. -/
theorem smoothInfinitesimalPoint_surjective_kernel
    (p : (smoothSquareZeroReduction W I).ker) :
    ∃ x : I, smoothInfinitesimalPoint W I hI x = p.val := by
  have hr : squareZeroQuotientTestMap I ≫ p.val = 1 := p.property
  have hi := congrArg (fun q ↦ q.left ≫ (integralSmoothOpen W).ι) hr
  rw [smoothGroupPoint_one_inclusion] at hi
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ p.val.left) ≫ _ = _ at hi
  rw [Category.assoc] at hi
  obtain ⟨x, hx⟩ := exists_infinitesimal_chart_parameter W I hI
    (p.val.left ≫ (integralSmoothOpen W).ι) (by
      rw [Category.assoc]
      exact p.val.w) hi
  refine ⟨x, Over.OverMorphism.ext ?_⟩
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [smoothInfinitesimalPoint_inclusion]
  exact hx

/-- The parameter homomorphism lands in the actual reduction kernel. -/
def smoothInfinitesimalKernelHom :
    Multiplicative I →* (smoothSquareZeroReduction W I).ker where
  toFun x := ⟨smoothInfinitesimalPoint W I hI x.toAdd,
    smoothInfinitesimalPoint_reduction W I hI x.toAdd⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg Additive.toMul (smoothInfinitesimalPointAddHom W I hI).map_zero
  map_mul' x y := Subtype.ext (smoothInfinitesimalPoint_add W I hI x.toAdd y.toAdd)

/-- The original chart parameter gives a bijection onto the entire reduction kernel. -/
theorem smoothInfinitesimalKernelHom_bijective :
    Function.Bijective (smoothInfinitesimalKernelHom W I hI) := by
  constructor
  · intro x y h
    exact smoothInfinitesimalPoint_injective W I hI (congrArg Subtype.val h)
  · intro p
    obtain ⟨x, hx⟩ := smoothInfinitesimalPoint_surjective_kernel W I hI p
    exact ⟨Multiplicative.ofAdd x, Subtype.ext hx⟩

/-- The square-zero kernel is the additive ideal, with its constructed group law. -/
def smoothSquareZeroKernelEquiv : Multiplicative I ≃* (smoothSquareZeroReduction W I).ker :=
  MulEquiv.ofBijective (smoothInfinitesimalKernelHom W I hI)
    (smoothInfinitesimalKernelHom_bijective W I hI)

end FLT.Mazur.WeierstrassIntegralChart

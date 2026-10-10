/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticE0SectionEquiv
public import FLT.Mazur.WeierstrassSmoothNegation

/-!
# Identity, inverse, and the reduction kernel of the actual integral sections

Separatedness extends the known generic zero and inverse formulas to the
integral section. On E₀ the geometric closed restriction equals the smooth
zero section exactly for the original arithmetic subgroup E₁.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- The section of the original identity is the actual infinity section. -/
theorem integralPointSection_zero :
    integralPointSection A W 0 = integralCurveZero W := by
  symm
  apply integralPointSection_unique A W 0
  · exact integralCurveZero_structure W
  · exact (projectiveToIntegral_zero W).symm

/-- The section construction commutes with the actual integral negation morphism. -/
theorem integralPointSection_neg
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    integralPointSection A W (-P) = integralPointSection A W P ≫ integralCurveNegation W := by
  symm
  apply integralPointSection_unique A W (-P)
  · rw [Category.assoc, integralCurveNegation_structure, integralPointSection_structure]
  · rw [← Category.assoc, integralPointSection_generic]
    exact (projectiveToIntegral_neg W P).symm

/-- The E₀ section equivalence preserves the actual smooth zero section. -/
theorem e0SmoothSectionEquiv_zero :
    (e0SmoothSectionEquiv A W 0).left = integralSmoothZero W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [integralSmoothZero_inclusion]
  exact (smoothIntegralPointSection_inclusion A W 0 (smoothReduction_zero A W)).trans
    (integralPointSection_zero A W)

/-- The E₀ section equivalence preserves the actual geometric inverse. -/
theorem e0SmoothSectionEquiv_neg (P : ellipticE0 A W) :
    (e0SmoothSectionEquiv A W (-P)).left =
      (e0SmoothSectionEquiv A W P).left ≫ integralSmoothNegation W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [Category.assoc, integralSmoothNegation_inclusion, ← Category.assoc]
  change smoothIntegralPointSection A W (-P.val) (-P).property ≫ _ =
    (smoothIntegralPointSection A W P.val P.property ≫ _) ≫ _
  rw [smoothIntegralPointSection_inclusion, smoothIntegralPointSection_inclusion,
    integralPointSection_neg]

/-- The geometric closed restriction is zero exactly on the original arithmetic E₁. -/
theorem e0SmoothSectionEquiv_special_zero_iff (P : ellipticE0 A W) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        (e0SmoothSectionEquiv A W P).left =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ integralSmoothZero W ↔
        P.val ∈ ellipticE1 A W := by
  rw [← e0SmoothSectionEquiv_zero A W, e0SmoothSectionEquiv_special,
    e0SmoothSectionEquiv_special, map_zero]
  have hi : Function.Injective (projectiveToSmooth (K := IsLocalRing.ResidueField A) W) := by
    intro x y h
    apply projectiveToSmoothOver_injective W
    exact Over.OverMorphism.ext h
  exact hi.eq_iff.trans (mem_smoothReductionHom_ker_iff A W P)

end FLT.Mazur.WeierstrassIntegralChart

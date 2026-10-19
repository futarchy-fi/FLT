/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluTargetGroupMorphism
public import FLT.FreyCurve.VeluPadicMinimalModel
public import FLT.Mazur.RationalPadicMinimalGroupMorphism

/-!
# The actual Frey quotient on local minimal generic fibers

The original rational group quotient and its rational torsion embedding give
minimal source and target equations at every prime. Their generic morphism has
degree p, recovers the rational map, and retains the specified target p-subgroup.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry WeierstrassCurve WeierstrassCurve.Velu
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

namespace FreyPackage

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing
  padicIntegerSubring_residue_finite

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- The retained target has the actual degree-p quotient on its minimal local generic model. -/
theorem IsVeluTarget.exists_padic_minimal_generic_quotient (h : P.IsVeluTarget E)
    (hne : E ≠ P.freyCurve) (hp17 : 17 ≤ P.p)
    (l : ℕ) [Fact l.Prime] [DecidableEq ℚ_[l]] :
    ∃ (hE : E.IsElliptic)
      (F : integralCurveGroup P.freyCurve IsElliptic.isUnit ⟶ integralCurveGroup E hE.isUnit)
      (φ : (P.freyCurve.toAffine.baseChange ℚ).Point →+ (E.toAffine.baseChange ℚ).Point)
      (f : ZMod P.p →+ (E.toAffine.baseChange ℚ).Point)
      (W U : WeierstrassCurve (padicIntegerSubring l)) (C D : VariableChange ℚ_[l])
      (hC : C • P.freyCurve.map (algebraMap ℚ ℚ_[l]) =
        W.map (algebraMap (padicIntegerSubring l) ℚ_[l]))
      (hD : D • E.map (algebraMap ℚ ℚ_[l]) =
        U.map (algebraMap (padicIntegerSubring l) ℚ_[l]))
      (hW : (W.map (algebraMap (padicIntegerSubring l) ℚ_[l])).IsElliptic)
      (hU : (U.map (algebraMap (padicIntegerSubring l) ℚ_[l])).IsElliptic)
      (g : integralCurveGroup (W.map (algebraMap (padicIntegerSubring l) ℚ_[l])) hW.isUnit ⟶
        integralCurveGroup (U.map (algebraMap (padicIntegerSubring l) ℚ_[l])) hU.isUnit),
      FLT.Mazur.FCurve.FiniteLocallyFreeDegree F.hom.hom.hom.left P.p ∧
      (∀ a, (affineSmoothPoint P.freyCurve a ≫ (integralSmoothOpen P.freyCurve).ι) ≫
        F.hom.hom.hom.left = affineSmoothPoint E (φ a) ≫ (integralSmoothOpen E).ι) ∧
      Function.Injective f ∧
      IsMinimal (padicIntegerSubring l)
        (W.map (algebraMap (padicIntegerSubring l) ℚ_[l])) ∧
      IsMinimal (padicIntegerSubring l)
        (U.map (algebraMap (padicIntegerSubring l) ℚ_[l])) ∧
      FLT.Mazur.FCurve.FiniteLocallyFreeDegree g.hom.hom.hom.left P.p ∧
      (g.hom.hom.hom.left ≫ (integralVariableChangeIso _ _ D hD).hom ≫
          integralCoefficientMorphism E =
        (integralVariableChangeIso _ _ C hC).hom ≫
          integralCoefficientMorphism P.freyCurve ≫ F.hom.hom.hom.left) ∧
      let fU := (rationalPadicProjectiveHom l E U D hD).comp f
      Function.Injective fU ∧ addOrderOf (fU 1) = P.p ∧
      ((U.map (algebraMap (padicIntegerSubring l) ℚ_[l])).HasGoodReduction
        (padicIntegerSubring l) ∨
      (U.map (algebraMap (padicIntegerSubring l) ℚ_[l])).HasMultiplicativeReduction
        (padicIntegerSubring l)) := by
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  obtain ⟨q, hq, hfixed, heq, hE, F, φ, f, hdeg, _, _, hf, hφ, _, _⟩ :=
    h.exists_prime_group_morphism hne
  let _ := hE
  obtain ⟨W, U, C, D, hC, hD, hW, hU, g, hmW, hmU, hg, hsq⟩ :=
    exists_padic_minimal_group_morphism l P.freyCurve E F P.p hdeg
  let _ := hmU
  let _ := hU
  let fU := (rationalPadicProjectiveHom l E U D hD).comp f
  have hi : Function.Injective fU := (rationalPadicProjectiveHom_injective l E U D hD).comp hf
  have ho : addOrderOf (fU 1) = P.p :=
    (addOrderOf_injective fU hi 1).trans (ZMod.addOrderOf_one P.p)
  have hn : P.p • fU 1 = 0 := by
    simpa only [ho] using addOrderOf_nsmul_eq_zero (fU 1)
  have hneU : fU 1 ≠ 0 := by
    intro hz
    exact one_ne_zero (hi (hz.trans (map_zero fU).symm))
  exact ⟨hE, F, φ, f, W, U, C, D, hC, hD, hW, hU, g, hdeg, hφ, hf,
    hmW, hmU, hg, hsq, hi, ho, padic_semistable_of_prime_torsion l U P.p hp17 (fU 1) hneU hn⟩

end FreyPackage

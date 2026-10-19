/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RationalPadicMinimalTransport
public import FLT.Mazur.WeierstrassGroupHomCoefficient
public import FLT.Mazur.WeierstrassGroupHomVariableChange

/-!
# Actual maps on the generic fibers of p-adic minimal equations

Choose the original source and target minimalizations, extend the given rational
group map, and conjugate by their actual coordinate changes. The degree and
the square back to the original rational map are proved for the constructed map.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace FLT.Mazur

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing

variable (q : ℕ) [Fact q.Prime]
  (E V : WeierstrassCurve ℚ) [E.IsElliptic] [V.IsElliptic]
  (f : integralCurveGroup E IsElliptic.isUnit ⟶ integralCurveGroup V IsElliptic.isUnit)
  (d : ℕ) (hd : FCurve.FiniteLocallyFreeDegree f.hom.hom.hom.left d)

include hd

/-- Both actual minimal models carry the same generic quotient and its original degree. -/
theorem exists_padic_minimal_group_morphism :
    ∃ (W U : WeierstrassCurve (padicIntegerSubring q)) (C D : VariableChange ℚ_[q])
      (hC : C • E.map (algebraMap ℚ ℚ_[q]) =
        W.map (algebraMap (padicIntegerSubring q) ℚ_[q]))
      (hD : D • V.map (algebraMap ℚ ℚ_[q]) =
        U.map (algebraMap (padicIntegerSubring q) ℚ_[q]))
      (hW : (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).IsElliptic)
      (hU : (U.map (algebraMap (padicIntegerSubring q) ℚ_[q])).IsElliptic)
      (g : integralCurveGroup (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])) hW.isUnit ⟶
        integralCurveGroup (U.map (algebraMap (padicIntegerSubring q) ℚ_[q])) hU.isUnit),
      IsMinimal (padicIntegerSubring q)
        (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])) ∧
      IsMinimal (padicIntegerSubring q)
        (U.map (algebraMap (padicIntegerSubring q) ℚ_[q])) ∧
      FCurve.FiniteLocallyFreeDegree g.hom.hom.hom.left d ∧
      g.hom.hom.hom.left ≫ (integralVariableChangeIso _ _ D hD).hom ≫
          integralCoefficientMorphism V =
        (integralVariableChangeIso _ _ C hC).hom ≫
          integralCoefficientMorphism E ≫ f.hom.hom.hom.left := by
  classical
  obtain ⟨W, C, hC, hmW, _⟩ := exists_rational_padic_minimal_transport q E
  obtain ⟨U, D, hD, hmU, _⟩ := exists_rational_padic_minimal_transport q V
  have hW : (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).IsElliptic := by
    rw [← hC]
    infer_instance
  have hU : (U.map (algebraMap (padicIntegerSubring q) ℚ_[q])).IsElliptic := by
    rw [← hD]
    infer_instance
  let fK := integralGroupHomCoefficient (S := ℚ_[q]) E V IsElliptic.isUnit
    IsElliptic.isUnit IsElliptic.isUnit IsElliptic.isUnit f
  let g := integralGroupHomVariableChange _ _ _ _ C D hC hD
    IsElliptic.isUnit IsElliptic.isUnit hW.isUnit hU.isUnit fK
  refine ⟨W, U, C, D, hC, hD, hW, hU, g, hmW, hmU, ?_, ?_⟩
  · exact integralGroupHomVariableChange_degree _ _ _ _ C D hC hD _ _ _ _ fK d
      (integralGroupHomCoefficient_degree E V _ _ _ _ f d hd)
  · change (integralGroupHomVariableChange _ _ _ _ C D hC hD _ _ _ _ fK).hom.hom.hom.left ≫
      (integralVariableChangeIso _ _ D hD).hom ≫ integralCoefficientMorphism V = _
    rw [integralGroupHomVariableChange_square_assoc]
    change _ ≫ (integralGroupHomCoefficient E V _ _ _ _ f).hom.hom.hom.left ≫ _ = _
    rw [integralGroupHomCoefficient_square]

end FLT.Mazur

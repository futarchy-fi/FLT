/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticGoodReductionModelSections
public import FLT.Mazur.EllipticGoodComponent
public import FLT.Mazur.EllipticIntegralSectionIdentity

/-!
# Every original point in the good-reduction generalized model

Unit discriminant puts every original generic point in E₀. The actual section
group of the genuine generalized model is therefore additively equivalent to
the entire original point group, preserving generic restriction and reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (hΔ : IsUnit W.Δ)

include hΔ in
/-- Unit discriminant gives smooth reduction for each original generic point. -/
theorem goodReduction_originalPoint_smooth
    (P : (W.map (algebraMap A K)).toProjective.Point) : SmoothReduction A W P := by
  let _ : W.IsElliptic := ⟨hΔ⟩
  exact smoothReduction_of_isElliptic A W P

/-- In good reduction E₀ contains every original point, with its unchanged addition. -/
def goodReductionPointsE0Equiv :
    (W.map (algebraMap A K)).toProjective.Point ≃+ ellipticE0 A W where
  toFun P := ⟨P, goodReduction_originalPoint_smooth A W hΔ P⟩
  invFun P := P.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The whole original point group is the actual group of generalized-model sections. -/
def goodReductionOriginalPointAddEquiv :
    (W.map (algebraMap A K)).toProjective.Point ≃+
      Additive (goodReductionModelSections A W hΔ) :=
  (goodReductionPointsE0Equiv A W hΔ).trans (e0GoodReductionModelAddEquiv A W hΔ)

/-- The equivalence is given by the original integral section at every point. -/
theorem goodReductionOriginalPointAddEquiv_left
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    ((goodReductionOriginalPointAddEquiv A W hΔ P).toMul).left =
      integralPointSection A W P :=
  e0ToGoodReductionModel_left A W hΔ (goodReductionPointsE0Equiv A W hΔ P)

/-- The actual original generic point is recovered by restriction. -/
theorem goodReductionOriginalPointAddEquiv_generic
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
        ((goodReductionOriginalPointAddEquiv A W hΔ P).toMul).left =
      (projectiveToIntegral W P).left := by
  rw [goodReductionOriginalPointAddEquiv_left, integralPointSection_generic]

/-- Specialization agrees with the existing arithmetic smooth reduction point. -/
theorem goodReductionOriginalPointAddEquiv_special
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        ((goodReductionOriginalPointAddEquiv A W hΔ P).toMul).left =
      (projectiveToIntegral W
        (smoothReductionHom A W (goodReductionPointsE0Equiv A W hΔ P))).left := by
  rw [goodReductionOriginalPointAddEquiv_left]
  exact integralPointSpecialization_eq_projective A W P
    (goodReduction_originalPoint_smooth A W hΔ P)

/-- The exact additive order of each original torsion generator survives in the model. -/
theorem goodReductionOriginalPointAddEquiv_order
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    addOrderOf (goodReductionOriginalPointAddEquiv A W hΔ P) = addOrderOf P :=
  (goodReductionOriginalPointAddEquiv A W hΔ).addOrderOf_eq P

end FLT.Mazur.WeierstrassIntegralChart

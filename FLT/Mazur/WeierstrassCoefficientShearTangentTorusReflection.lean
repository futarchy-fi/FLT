/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTorusReflection
public import FLT.Mazur.WeierstrassCoefficientShearTangentRootEvaluation

/-!
# Laurent inversion for the actual integral tangent action

The complete chosen-root action specializes into the original tangent model.
Its actual conjugation inverts the torus parameter on arbitrary test schemes,
while carrying the entire model input through the constructed companion change.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
  (hr : r ^ 2 + (W.map (algebraMap R S)).a₁ * r - (W.map (algebraMap R S)).a₂ = 0)
  (h3 : (W.map (algebraMap R S)).a₃ = 0)
  (h4 : (W.map (algebraMap R S)).a₄ = 0)
  (h6 : (W.map (algebraMap R S)).a₆ = 0)
local notation "V" => W.map (algebraMap R S)
local notation "s" => (-(V).a₁ - r)
local notation "hb" => rootShearOpposite_tangent V r a ha
local notation "hs" => rootShearOpposite_root V r hr
local notation "ι" => Spec.map (CommRingCat.ofHom
  (LaurentPolynomial.invert (R := S)).toRingHom)
local notation "C" => coefficientShearRootChange hπ data S r s j hj
local notation "g" => Over.hom (MultiplicativeGroupScheme.gm S)
local notation "gr" => coefficientShearGluedStructure hπ data S r j hj
local notation "gs" => coefficientShearGluedStructure hπ data S s j hj
local notation "Ar" => coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6
local notation "As" => coefficientShearTorusAction hπ data S s j hj (-a) hb hs h3 h4 h6

local notation "Mr" => coefficientShearTangentRootSpecialization hπ data S r hr j hj
local notation "Ms" => coefficientShearTangentRootSpecialization hπ data S s hs j hj
local notation "σ" => coefficientShearTangentConjugation hπ data j hj

variable {T : Scheme} (p : T ⟶ (MultiplicativeGroupScheme.gm S).left)
  (q : T ⟶ coefficientShearGlued hπ data S r j hj)
  (hpq : p ≫ Over.hom (MultiplicativeGroupScheme.gm S) =
    q ≫ coefficientShearGluedStructure hπ data S r j hj)

/-- The genuine integral tangent conjugation has the actual inverse torus orientation. -/
theorem coefficientShearTangentTorusReflection_actionPair :
    pullback.lift p q hpq ≫ Ar ≫ Mr ≫ σ =
      pullback.lift (p ≫ ι) (q ≫ (C).hom)
          (coefficientShearTorusReflection_condition
            hπ data S r j hj a ha hr h3 h4 h6 p q hpq) ≫ As ≫ Ms := by
  have hrt : r + s = -algebraMap R S W.a₁ := by
    change r + (-algebraMap R S W.a₁ - r) = -algebraMap R S W.a₁
    ring
  rw [coefficientShearTangentRootSpecialization_conjugation
    hπ data S r hr j hj s hs hrt]
  have H := coefficientShearTorusReflection_actionPair
    hπ data S r j hj a ha hr h3 h4 h6 p q hpq
  simpa only [Category.assoc] using congrArg (fun f => f ≫ Ms) H.symm

end FLT.Mazur.WeierstrassDividedDepth

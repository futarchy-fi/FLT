/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootTorusChange
public import FLT.Mazur.WeierstrassRootShearTorusReflection

/-!
# Explicit Laurent inversion on the complete chosen-root torus action

The parameter comparison is computed through both actual smooth variable
changes. Reflection of the whole model intertwines the full action domains.
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
local notation "P" => coefficientShearRootTorusParameter S r s a (-a) ha hb hr hs h3 h4 h6
local notation "ι" => Spec.map (CommRingCat.ofHom
  (LaurentPolynomial.invert (R := S)).toRingHom)
local notation "C" => coefficientShearRootChange hπ data S r s j hj
local notation "g" => Over.hom (MultiplicativeGroupScheme.gm S)
local notation "gr" => coefficientShearGluedStructure hπ data S r j hj
local notation "gs" => coefficientShearGluedStructure hπ data S s j hj
local notation "Ar" => coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6
local notation "As" => coefficientShearTorusAction hπ data S s j hj (-a) hb hs h3 h4 h6

omit [IsDomain R] [IsBezout R] in
/-- The full coefficient-model parameter comparison is the signed Laurent inversion. -/
theorem coefficientShearRootTorusParameter_reflection : (P).hom = ι :=
  rootShearTorusParameter_reflection V r a ha hr h3 h4 h6

variable {T : Scheme} (p : T ⟶ (MultiplicativeGroupScheme.gm S).left)
  (q : T ⟶ coefficientShearGlued hπ data S r j hj)
  (hpq : p ≫ Over.hom (MultiplicativeGroupScheme.gm S) =
    q ≫ coefficientShearGluedStructure hπ data S r j hj)

include hpq ha hr h3 h4 h6 in
/-- Inversion and whole-model reflection preserve the actual torus domain condition. -/
theorem coefficientShearTorusReflection_condition : (p ≫ ι) ≫ g = (q ≫ (C).hom) ≫ gs := by
  rw [← coefficientShearRootTorusParameter_reflection S r a ha hr h3 h4 h6]
  exact coefficientShearRootTorusPair_condition hπ data S r s j hj a (-a)
    ha hb hr hs h3 h4 h6 p q hpq

/-- The actual actions on arbitrary scheme-valued inputs differ by Laurent inversion. -/
theorem coefficientShearTorusReflection_actionPair :
    pullback.lift (p ≫ ι) (q ≫ (C).hom)
        (coefficientShearTorusReflection_condition hπ data S r j hj a ha hr h3 h4 h6 p q hpq) ≫
      As = pullback.lift p q hpq ≫ Ar ≫ (C).hom := by
  have H := coefficientShearRootTorusChange_actionPair hπ data S r s j hj a (-a)
    ha hb hr hs h3 h4 h6 p q hpq
  refine Eq.trans ?_ H.symm
  apply congrArg (fun f => f ≫ As)
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
    exact congrArg (fun f => p ≫ f)
      (coefficientShearRootTorusParameter_reflection S r a ha hr h3 h4 h6).symm
  · simp only [pullback.lift_snd]

/-- Both full-domain projections keep the actual inverted parameter and reflected model. -/
theorem coefficientShearTorusReflection_domain :
    coefficientShearRootTorusChangeDomain hπ data S r s j hj a (-a)
      ha hb hr hs h3 h4 h6 =
    pullback.lift (pullback.fst g gr ≫ ι) (pullback.snd g gr ≫ (C).hom)
      (coefficientShearTorusReflection_condition hπ data S r j hj a ha hr h3 h4 h6
        (pullback.fst g gr) (pullback.snd g gr) pullback.condition) := by
  unfold coefficientShearRootTorusChangeDomain
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
    exact congrArg (fun f => pullback.fst g gr ≫ f)
      (coefficientShearRootTorusParameter_reflection S r a ha hr h3 h4 h6)
  · simp only [pullback.lift_snd]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbit
public import FLT.Mazur.WeierstrassCoefficientShearTorusDomain

/-!
# The full torus action retains arbitrary scheme-valued input pairs

The actual torus domain comparison is evaluated on both input legs. The
model input may lie on an exceptional component and the test scheme may be nonreduced.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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
local notation "f" => integralSmoothStructure V
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm S)
local notation "I" => rootShearTorusSmoothIso V r a ha hr h3 h4 h6
local notation "D" => coefficientShearTorusDomainMap hπ data S r j hj a ha hr h3 h4 h6
local notation "B" => coefficientShearSmoothEmbedding hπ data S r j hj

/-- The torus parameter gives the genuine smooth input over the model point's coefficient map. -/
theorem coefficientShearTorusPair_condition {T : Scheme}
    (p : T ⟶ (MultiplicativeGroupScheme.gm S).left)
    (q : T ⟶ coefficientShearGlued hπ data S r j hj) (hpq : p ≫ t = q ≫ g) :
    (p ≫ (I).hom) ≫ f = q ≫ g := by
  rw [Category.assoc, rootShearTorusSmoothIso_structure]
  exact hpq

/-- Both actual inputs are retained on the entire torus action domain. -/
theorem coefficientShearTorusPair_domain {T : Scheme}
    (p : T ⟶ (MultiplicativeGroupScheme.gm S).left)
    (q : T ⟶ coefficientShearGlued hπ data S r j hj) (hpq : p ≫ t = q ≫ g) :
    pullback.lift p q hpq ≫ D = pullback.lift (p ≫ (I).hom) q
      (coefficientShearTorusPair_condition hπ data S r j hj a ha hr h3 h4 h6 p q hpq) := by
  apply pullback.hom_ext
  · rw [Category.assoc, coefficientShearTorusDomainMap_parameter,
      pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, coefficientShearTorusDomainMap_model,
      pullback.lift_snd, pullback.lift_snd]

/-- On arbitrary scheme-valued pairs the torus action is the original smooth action. -/
theorem coefficientShearTorusAction_pair {T : Scheme}
    (p : T ⟶ (MultiplicativeGroupScheme.gm S).left)
    (q : T ⟶ coefficientShearGlued hπ data S r j hj) (hpq : p ≫ t = q ≫ g) :
    pullback.lift p q hpq ≫
        coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6 =
      pullback.lift (p ≫ (I).hom) q
        (coefficientShearTorusPair_condition hπ data S r j hj a ha hr h3 h4 h6 p q hpq) ≫
          coefficientShearAction hπ data S r j hj := by
  rw [coefficientShearTorusAction, ← Category.assoc]
  change (pullback.lift p q hpq ≫ D) ≫ _ = _
  rw [coefficientShearTorusPair_domain]

end FLT.Mazur.WeierstrassDividedDepth

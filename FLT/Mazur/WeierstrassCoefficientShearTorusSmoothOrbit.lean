/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbit
public import FLT.Mazur.WeierstrassCoefficientShearTorusDomain
public import FLT.Mazur.WeierstrassRootShearUnitAddition

/-!
# The full sheared torus action multiplies units on the original smooth orbit

Both the parameter and model point use the actual root-sheared smooth input.
The result is computed by the independently constructed global action, for
arbitrary algebra-valued units, including nonreduced source algebras.
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
local notation "B" => coefficientShearSmoothEmbedding hπ data S r j hj
local notation "I" => rootShearTorusSmoothIso V r a ha hr h3 h4 h6
local notation "D" => coefficientShearTorusDomainMap hπ data S r j hj a ha hr h3 h4 h6
variable {A : Type} [CommRing A] [Algebra S A] (p q : Aˣ)
local notation "P" => rootShearSmoothUnitInput V r a ha hr h3 h4 h6 p
local notation "Q" => rootShearSmoothUnitInput V r a ha hr h3 h4 h6 q
local notation "u" => laurentUnitOverPoint (R := S) p

/-- The actual Laurent parameter and original smooth-orbit point have the same base. -/
theorem coefficientShearTorusSmoothPair_condition :
    (u).left ≫ t = ((Q).left ≫ B) ≫ g := by
  rw [Category.assoc, coefficientShearSmoothEmbedding_structure]
  exact (u).w.trans (Q).w.symm

local notation "hpq" => coefficientShearTorusSmoothPair_condition
  hπ data S r j hj a ha hr h3 h4 h6 p q

/-- The complete torus-domain comparison retains both independently defined smooth inputs. -/
theorem coefficientShearTorusSmoothPair_domain :
    pullback.lift (u).left ((Q).left ≫ B) hpq ≫ D =
      pullback.lift (P).left ((Q).left ≫ B)
        (by rw [Category.assoc, coefficientShearSmoothEmbedding_structure]
            exact (P).w.trans (Q).w.symm) := by
  apply pullback.hom_ext
  · rw [Category.assoc, coefficientShearTorusDomainMap_parameter,
      pullback.lift_fst_assoc, pullback.lift_fst]
    rfl
  · rw [Category.assoc, coefficientShearTorusDomainMap_model,
      pullback.lift_snd, pullback.lift_snd]

/-- The original global action multiplies unit parameters on its entire smooth orbit. -/
theorem coefficientShearTorusAction_smoothUnits :
    pullback.lift (u).left ((Q).left ≫ B) hpq ≫
        coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6 =
      (rootShearSmoothUnitInput V r a ha hr h3 h4 h6 (p * q)).left ≫ B := by
  rw [coefficientShearTorusAction, ← Category.assoc]
  change (pullback.lift (u).left ((Q).left ≫ B) hpq ≫ D) ≫ _ = _
  rw [coefficientShearTorusSmoothPair_domain,
    coefficientShearAction_smoothEmbedding hπ data S r j hj (P).left (Q).left
      ((P).w.trans (Q).w.symm), rootShearSmoothUnitInput_addition]

end FLT.Mazur.WeierstrassDividedDepth

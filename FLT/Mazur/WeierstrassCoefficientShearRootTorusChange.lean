/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootChange
public import FLT.Mazur.WeierstrassCoefficientShearTorusPair

/-!
# Full torus action transport between two chosen tangent roots

The parameter comparison uses both actual smooth variable changes on the
original cubic. The entire model and action domain change compatibly over any coefficient algebra.
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
  (S : Type) [CommRing S] [Algebra R S] (r s : S) (j : ℕ) (hj : j ≤ n)
  (a b : Sˣ)
  (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
  (hb : (b : S) = (W.map (algebraMap R S)).a₁ + 2 * s)
  (hr : r ^ 2 + (W.map (algebraMap R S)).a₁ * r - (W.map (algebraMap R S)).a₂ = 0)
  (hs : s ^ 2 + (W.map (algebraMap R S)).a₁ * s - (W.map (algebraMap R S)).a₂ = 0)
  (h3 : (W.map (algebraMap R S)).a₃ = 0)
  (h4 : (W.map (algebraMap R S)).a₄ = 0)
  (h6 : (W.map (algebraMap R S)).a₆ = 0)
local notation "V" => W.map (algebraMap R S)
local notation "f" => integralSmoothStructure V
local notation "gr" => coefficientShearGluedStructure hπ data S r j hj
local notation "gs" => coefficientShearGluedStructure hπ data S s j hj
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm S)
local notation "Ir" => rootShearTorusSmoothIso V r a ha hr h3 h4 h6
local notation "Is" => rootShearTorusSmoothIso V s b hb hs h3 h4 h6
local notation "C" => coefficientShearRootChange hπ data S r s j hj

/-- Change the actual torus parameter through the two original smooth variable changes. -/
def coefficientShearRootTorusParameter :
    (MultiplicativeGroupScheme.gm S).left ≅ (MultiplicativeGroupScheme.gm S).left :=
  Ir ≪≫ (Is).symm
local notation "P" => coefficientShearRootTorusParameter S r s a b ha hb hr hs h3 h4 h6

omit [IsDomain R] [IsBezout R] in
/-- Every original smooth cubic function agrees under the changed parameter. -/
@[reassoc] theorem coefficientShearRootTorusParameter_smooth : (P).hom ≫ (Is).hom = (Ir).hom := by
  simp only [coefficientShearRootTorusParameter, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [IsDomain R] [IsBezout R] in
/-- The actual coefficient map is unchanged by the two smooth variable changes. -/
@[reassoc] theorem coefficientShearRootTorusParameter_structure : (P).hom ≫ t = t := by
  rw [← rootShearTorusSmoothIso_structure V s b hb hs h3 h4 h6,
    coefficientShearRootTorusParameter_smooth_assoc,
    rootShearTorusSmoothIso_structure, rootShearTorusSmoothIso_structure]

variable {T : Scheme} (p : T ⟶ (MultiplicativeGroupScheme.gm S).left)
  (q : T ⟶ coefficientShearGlued hπ data S r j hj)
  (hpq : p ≫ Over.hom (MultiplicativeGroupScheme.gm S) =
    q ≫ coefficientShearGluedStructure hπ data S r j hj)

include hpq in
/-- Both changed inputs lie in the actual new-root torus domain. -/
theorem coefficientShearRootTorusPair_condition :
    (p ≫ (P).hom) ≫ t = (q ≫ (C).hom) ≫ gs := by
  rw [Category.assoc, coefficientShearRootTorusParameter_structure,
    Category.assoc, coefficientShearRootChange_structure]
  exact hpq

/-- The genuine torus action intertwines both whole-model and actual smooth-parameter changes. -/
theorem coefficientShearRootTorusChange_actionPair :
    pullback.lift p q hpq ≫
        coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6 ≫ (C).hom =
      pullback.lift (p ≫ (P).hom) (q ≫ (C).hom)
          (coefficientShearRootTorusPair_condition hπ data S r s j hj a b
            ha hb hr hs h3 h4 h6 p q hpq) ≫
        coefficientShearTorusAction hπ data S s j hj b hb hs h3 h4 h6 := by
  rw [← Category.assoc, coefficientShearTorusAction_pair, coefficientShearTorusAction_pair]
  simp only [Category.assoc, coefficientShearRootTorusParameter_smooth]
  exact coefficientShearRootChange_actionPair hπ data S r s j hj _ q
    (coefficientShearTorusPair_condition hπ data S r j hj a ha hr h3 h4 h6 p q hpq)

/-- The complete torus domain comparison retains both changed original inputs. -/
def coefficientShearRootTorusChangeDomain :
    pullback t gr ⟶ pullback t gs :=
  pullback.lift (pullback.fst t gr ≫ (P).hom) (pullback.snd t gr ≫ (C).hom)
    (coefficientShearRootTorusPair_condition hπ data S r s j hj a b ha hb hr hs h3 h4 h6
      (pullback.fst t gr) (pullback.snd t gr) pullback.condition)

/-- The full new-root torus action is the old action transported on its entire domain. -/
@[reassoc] theorem coefficientShearRootTorusChange_action :
    coefficientShearRootTorusChangeDomain hπ data S r s j hj a b ha hb hr hs h3 h4 h6 ≫
        coefficientShearTorusAction hπ data S s j hj b hb hs h3 h4 h6 =
      coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6 ≫ (C).hom := by
  have H := coefficientShearRootTorusChange_actionPair hπ data S r s j hj a b
    ha hb hr hs h3 h4 h6 (pullback.fst t gr) (pullback.snd t gr) pullback.condition
  have hi : pullback.lift (pullback.fst t gr) (pullback.snd t gr) pullback.condition =
      𝟙 (pullback t gr) := by
    apply pullback.hom_ext <;>
      simp only [pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  rw [hi, Category.id_comp] at H
  exact H.symm

end FLT.Mazur.WeierstrassDividedDepth

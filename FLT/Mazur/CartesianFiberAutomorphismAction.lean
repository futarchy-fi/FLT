/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Actual automorphisms on a cartesian geometric fiber

Automorphisms of the coefficient test fixing the original base induce an
action on any specified cartesian fiber. The original projection is fixed
and the coefficient projection transforms by the supplied automorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CartesianFiberAutomorphismAction
set_option backward.isDefEq.respectTransparency false
variable {G : Type} [Group G] {Y V T S : Scheme}
  {a : Y ⟶ V} {b : Y ⟶ T} {f : V ⟶ S} {t : T ⟶ S}
  (H : IsPullback a b f t) (τ : G →* Aut T) (hτ : ∀ g, (τ g).hom ≫ t = t)

/-- The induced endomorphism with unchanged original coordinate. -/
def map (g : G) : Y ⟶ Y :=
  H.lift a (b ≫ (τ g).hom) (by rw [Category.assoc, hτ]; exact H.w)

@[reassoc (attr := simp)]
theorem map_fst (g : G) : map H τ hτ g ≫ a = a := H.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem map_snd (g : G) : map H τ hτ g ≫ b = b ≫ (τ g).hom := H.lift_snd _ _ _

@[simp]
theorem map_one : map H τ hτ 1 = 𝟙 Y := by
  apply H.hom_ext
  · simp
  · rw [map_snd, _root_.map_one]
    exact Category.comp_id b |>.trans (Category.id_comp b).symm

/-- Multiplication agrees with composition in the automorphism group. -/
theorem map_mul (g h : G) : map H τ hτ (g * h) = map H τ hτ h ≫ map H τ hτ g := by
  apply H.hom_ext
  · simp
  · simp only [map_snd, Category.assoc, map_snd_assoc, _root_.map_mul, Aut.Aut_mul_def,
      Iso.trans_hom]

/-- The constructed action by actual scheme isomorphisms. -/
def action : G →* Aut Y where
  toFun g :=
    { hom := map H τ hτ g
      inv := map H τ hτ g⁻¹
      hom_inv_id := by rw [← map_mul, inv_mul_cancel, map_one]
      inv_hom_id := by rw [← map_mul, mul_inv_cancel, map_one] }
  map_one' := Aut.ext (map_one H τ hτ)
  map_mul' g h := Aut.ext (map_mul H τ hτ g h)

@[reassoc (attr := simp)]
theorem action_fst (g : G) : (action H τ hτ g).hom ≫ a = a := map_fst H τ hτ g

@[reassoc (attr := simp)]
theorem action_snd (g : G) : (action H τ hτ g).hom ≫ b = b ≫ (τ g).hom :=
  map_snd H τ hτ g

end FLT.Mazur.CartesianFiberAutomorphismAction

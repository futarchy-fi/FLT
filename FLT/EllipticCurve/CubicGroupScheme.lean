/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicAssociativity
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # The smooth cubic as a commutative group scheme over a reduced noetherian base -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The constructed cubic as a scheme over its coefficient base. -/
abbrev groupModel : Over (Spec (.of R)) := Over.mk (toBase W)

/-- The infinity section as a morphism over the coefficient base. -/
def zeroOver : 𝟙_ (Over (Spec (.of R))) ⟶ groupModel W :=
  Over.homMk (infinity W) (infinity_toBase W)

/-- The globally descended addition as a morphism over the base. -/
def addOver [W.IsElliptic] : groupModel W ⊗ groupModel W ⟶ groupModel W :=
  Over.homMk (addition W) (addition_toBase W)

/-- The globally descended negation as a morphism over the base. -/
def negationOver : groupModel W ⟶ groupModel W :=
  Over.homMk (negation W) (negation_toBase W)

theorem zeroOver_mul [W.IsElliptic] :
    zeroOver W ▷ groupModel W ≫ addOver W = (λ_ (groupModel W)).hom := by
  have hp : (λ_ (groupModel W)).inv ≫ (zeroOver W ▷ groupModel W) =
      lift (toUnit (groupModel W) ≫ zeroOver W) (𝟙 (groupModel W)) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  apply (cancel_epi (λ_ (groupModel W)).inv).mp
  rw [← Category.assoc, hp, Iso.inv_hom_id]
  apply Over.OverMorphism.ext
  exact addition_zero_left W

theorem mul_zeroOver [W.IsElliptic] :
    groupModel W ◁ zeroOver W ≫ addOver W = (ρ_ (groupModel W)).hom := by
  have hp : (ρ_ (groupModel W)).inv ≫ (groupModel W ◁ zeroOver W) =
      lift (𝟙 (groupModel W)) (toUnit (groupModel W) ≫ zeroOver W) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  apply (cancel_epi (ρ_ (groupModel W)).inv).mp
  rw [← Category.assoc, hp, Iso.inv_hom_id]
  apply Over.OverMorphism.ext
  exact addition_zero_right W

theorem addOver_assoc [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    addOver W ▷ groupModel W ≫ addOver W =
      (α_ (groupModel W) (groupModel W) (groupModel W)).hom ≫
        groupModel W ◁ addOver W ≫ addOver W := by
  let C := groupModel W
  let a : (C ⊗ C) ⊗ C ⟶ C := fst (C ⊗ C) C ≫ fst C C
  let b : (C ⊗ C) ⊗ C ⟶ C := fst (C ⊗ C) C ≫ snd C C
  let c : (C ⊗ C) ⊗ C ⟶ C := snd (C ⊗ C) C
  have hp : lift a b = fst (C ⊗ C) C := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [a, b]
  have hl : addOver W ▷ C = lift (lift a b ≫ addOver W) c := by
    rw [hp]
    apply CartesianMonoidalCategory.hom_ext <;> simp [c, C]
  have hr : (α_ C C C).hom ≫ (C ◁ addOver W) =
      lift a (lift b c ≫ addOver W) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [a]
    · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
      rw [← Category.assoc]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [b, c]
  change (addOver W ▷ C) ≫ addOver W =
    (α_ C C C).hom ≫ (C ◁ addOver W) ≫ addOver W
  rw [hl, ← Category.assoc, hr]
  apply Over.OverMorphism.ext
  exact addMorphisms_assoc W a.left b.left c.left
    (a.w.trans b.w.symm) (a.w.trans c.w.symm)

instance groupModelMonObj [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    MonObj (groupModel W) where
  one := zeroOver W
  mul := addOver W
  one_mul := zeroOver_mul W
  mul_one := mul_zeroOver W
  mul_assoc := addOver_assoc W

instance groupModelGrpObj [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    GrpObj (groupModel W) where
  inv := negationOver W
  left_inv := by
    apply Over.OverMorphism.ext
    exact addition_inverse_left W
  right_inv := by
    apply Over.OverMorphism.ext
    exact addition_inverse_right W

instance groupModelCommGrpObj [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    CommGrpObj (groupModel W) where
  mul_comm := by
    apply Over.OverMorphism.ext
    exact addition_comm W

instance groupModel_proper : IsProper (groupModel W).hom := by
  change IsProper (toBase W)
  infer_instance

instance groupModel_smooth [W.IsElliptic] : Smooth (groupModel W).hom := by
  change Smooth (toBase W)
  infer_instance

instance groupModel_dimension_one [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (groupModel W).hom := by
  change SmoothOfRelativeDimension 1 (toBase W)
  infer_instance

instance groupModel_geometricallyConnected : GeometricallyConnected (groupModel W).hom := by
  change GeometricallyConnected (toBase W)
  infer_instance

end WeierstrassCurve.CubicCharts

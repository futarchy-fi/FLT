/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientBaseGroup

/-!
# Projecting a homomorphism into the base changed smooth group

Multiplication in any source group projects to actual smooth ambient addition.
The formula uses the original fiber product projections, without expanding
monoidal base change in subsequent descent arguments.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassDividedDepth

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (G : CommGrp (Over (Spec (.of S))))
  (f : G ⟶ originalSmoothBaseChangeGroup S W)

local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "j" => f.hom.hom.hom.left ≫ pullback.fst (integralSmoothStructure W) q

/-- The projected homomorphism retains the coefficient structure. -/
@[reassoc] theorem smoothBaseGroupHom_structure :
    j ≫ integralSmoothStructure W = G.X.hom ≫ q := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ q) (Over.w f.hom.hom.hom)

/-- The two projected group inputs have the same original coefficient structure. -/
theorem smoothBaseGroupHom_pair_condition :
    (pullback.fst G.X.hom G.X.hom ≫ j) ≫ integralSmoothStructure W =
      (pullback.snd G.X.hom G.X.hom ≫ j) ≫ integralSmoothStructure W := by
  rw [Category.assoc, smoothBaseGroupHom_structure, ← Category.assoc,
    pullback.condition, Category.assoc, ← smoothBaseGroupHom_structure, ← Category.assoc]

/-- Multiplication projects to the original integral smooth multiplication. -/
@[reassoc] theorem smoothBaseGroupHom_mul :
    μ[G.X].left ≫ j =
      pullback.lift (pullback.fst _ _ ≫ j) (pullback.snd _ _ ≫ j)
        (smoothBaseGroupHom_pair_condition W G f) ≫ smoothFactorAddition W := by
  have hm := congrArg Over.Hom.left (IsMonHom.mul_hom f.hom.hom.hom)
  change μ[G.X].left ≫ f.hom.hom.hom.left =
    (f.hom.hom.hom ⊗ₘ f.hom.hom.hom).left ≫
      μ[(originalSmoothBaseChangeGroup S W).X].left at hm
  rw [← Category.assoc, hm, Category.assoc, originalSmoothBaseChangeGroup_mul_fst,
    ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc]
    erw [Over.tensorHom_left_fst]
    rw [Category.assoc]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]
    erw [Over.tensorHom_left_snd]
    rw [Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth

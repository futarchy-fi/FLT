/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientPointAddition
public import FLT.Mazur.WeierstrassSmoothGroup

/-!
# Operations on the categorical base change of the smooth group

Projection formulas for the independently constructed categorical base change
make comparison with the intrinsic smooth operations possible without unfolding
monoidal constraints in subsequent proofs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => integralSmoothStructure W

/-- The categorical base change of the original smooth commutative group scheme. -/
def originalSmoothBaseChangeGroup : CommGrp (Over (Spec (.of S))) :=
  (Over.pullback q).mapCommGrp.obj (integralSmoothGroup W)

/-- The underlying relative scheme is the actual smooth fiber product. -/
theorem originalSmoothBaseChangeGroup_carrier :
    (originalSmoothBaseChangeGroup S W).X = Over.mk (pullback.snd base q) := rfl

/-- Its identity projects to the original zero after changing the coefficient spectrum. -/
@[reassoc] theorem originalSmoothBaseChangeGroup_one_fst :
    η[(originalSmoothBaseChangeGroup S W).X].left ≫ pullback.fst base q =
      q ≫ integralSmoothZero W := by
  change ((Functor.LaxMonoidal.ε (Over.pullback q)).left ≫
    ((Over.pullback q).map (integralSmoothOverZero W)).left) ≫ _ = _
  have hf : ((Over.pullback q).map (integralSmoothOverZero W)).left ≫
      pullback.fst base q = pullback.fst (𝟙 _) q ≫ integralSmoothZero W :=
    pullback.lift_fst _ _ _
  rw [Category.assoc, hf, ← Category.assoc, Over.ε_pullback_left]
  have hc : pullback.fst (𝟙 (Spec (.of R))) q = pullback.snd (𝟙 _) q ≫ q := by
    simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 _) (g := q))
  rw [hc, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Its product projects to the original addition on the pair of original projections. -/
@[reassoc] theorem originalSmoothBaseChangeGroup_mul_fst :
    μ[(originalSmoothBaseChangeGroup S W).X].left ≫ pullback.fst base q =
      pullback.lift (pullback.fst _ _ ≫ pullback.fst base q)
        (pullback.snd _ _ ≫ pullback.fst base q)
        (by simp only [Category.assoc, pullback.condition];
            exact congrArg (· ≫ q) pullback.condition) ≫ smoothFactorAddition W := by
  change ((Functor.LaxMonoidal.μ (Over.pullback q)
    (integralSmoothOver W) (integralSmoothOver W)).left ≫
    ((Over.pullback q).map (integralSmoothOverAddition W)).left) ≫ _ = _
  have hf : ((Over.pullback q).map (integralSmoothOverAddition W)).left ≫
      pullback.fst base q = pullback.fst _ q ≫ smoothFactorAddition W :=
    pullback.lift_fst _ _ _
  rw [Category.assoc, hf, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact Over.μ_pullback_left_fst_fst (f := q) (integralSmoothOver W) _
  · rw [Category.assoc, pullback.lift_snd]
    exact Over.μ_pullback_left_fst_snd (f := q) (integralSmoothOver W) _

end FLT.Mazur.WeierstrassDividedDepth

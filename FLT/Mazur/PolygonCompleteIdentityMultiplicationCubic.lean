/-
Copyright (E).hom.hom.hom.hom 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityCubicGroup
public import FLT.Mazur.PolygonCompleteIdentityActionTarget

/-!
# The original identity multiplication retains the cubic action

The comparison of products uses the actual coefficient transport. Both
projections and multiplication keep the original smooth contraction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "H" => completePointIdentityGroup K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "e" => completePointSmoothCubicIso K n h i
local notation "F" => Over.map (inv (Scheme.toSpecΓ (S)))
local notation "E" => completePointIdentityCubicGroupIso K n h i
attribute [local instance] completePointOriginalBaseBraided

/-- The original relative identity product mapped to the actual smooth cubic product. -/
def completeIdentitySmoothPair : ((G).X ⊗ (G).X).left ⟶ smoothFactorProduct (W) :=
  (Functor.LaxMonoidal.μ (F) (H).X (H).X).left ≫ ((E).hom.hom.hom.hom ⊗ₘ (E).hom.hom.hom.hom).left

/-- The product comparison retains the original first contraction. -/
@[reassoc] theorem completeIdentitySmoothPair_fst :
    completeIdentitySmoothPair K n h i ≫ pullback.fst _ _ =
      pullback.fst (G).X.hom (G).X.hom ≫ (e).hom := by
  have ht := congrArg Over.Hom.left (tensorHom_fst (E).hom.hom.hom.hom (E).hom.hom.hom.hom)
  have hf := congrArg Over.Hom.left (Functor.Monoidal.μ_fst (F) (H).X (H).X)
  change ((E).hom.hom.hom.hom ⊗ₘ (E).hom.hom.hom.hom).left ≫
    pullback.fst (integralSmoothStructure (W)) (integralSmoothStructure (W)) =
    pullback.fst (H).X.hom (H).X.hom ≫ (e).hom at ht
  change (Functor.LaxMonoidal.μ (F) (H).X (H).X).left ≫
    pullback.fst (H).X.hom (H).X.hom = pullback.fst (G).X.hom (G).X.hom at hf
  exact (Category.assoc _ _ _).trans ((congrArg
    (fun f ↦ (Functor.LaxMonoidal.μ (F) (H).X (H).X).left ≫ f) ht).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (e).hom) hf)))

/-- The product comparison retains the original second contraction. -/
@[reassoc] theorem completeIdentitySmoothPair_snd :
    completeIdentitySmoothPair K n h i ≫ pullback.snd _ _ =
      pullback.snd (G).X.hom (G).X.hom ≫ (e).hom := by
  have ht := congrArg Over.Hom.left (tensorHom_snd (E).hom.hom.hom.hom (E).hom.hom.hom.hom)
  have hf := congrArg Over.Hom.left (Functor.Monoidal.μ_snd (F) (H).X (H).X)
  change ((E).hom.hom.hom.hom ⊗ₘ (E).hom.hom.hom.hom).left ≫
    pullback.snd (integralSmoothStructure (W)) (integralSmoothStructure (W)) =
    pullback.snd (H).X.hom (H).X.hom ≫ (e).hom at ht
  change (Functor.LaxMonoidal.μ (F) (H).X (H).X).left ≫
    pullback.snd (H).X.hom (H).X.hom = pullback.snd (G).X.hom (G).X.hom at hf
  exact (Category.assoc _ _ _).trans ((congrArg
    (fun f ↦ (Functor.LaxMonoidal.μ (F) (H).X (H).X).left ≫ f) ht).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (e).hom) hf)))

/-- Actual multiplication over the original base contracts to smooth cubic addition. -/
@[reassoc] theorem completeIdentitySmoothPair_addition :
    (μ[(G).X]).left ≫ (e).hom =
      completeIdentitySmoothPair K n h i ≫ smoothFactorAddition (W) := by
  have hm := congrArg Over.Hom.left (IsMonHom.mul_hom (E).hom.hom.hom.hom)
  change (μ[(H).X]).left ≫ (e).hom =
    ((E).hom.hom.hom.hom ⊗ₘ (E).hom.hom.hom.hom).left ≫ smoothFactorAddition (W) at hm
  change ((Functor.LaxMonoidal.μ (F) (H).X (H).X).left ≫
    (μ[(H).X]).left) ≫ (e).hom = _
  rw [Category.assoc, hm, completeIdentitySmoothPair, Category.assoc]

end FLT.Mazur.PolygonInfinitesimalStages

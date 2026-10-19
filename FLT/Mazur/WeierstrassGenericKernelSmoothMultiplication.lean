/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosurePairComparison
public import FLT.Mazur.WeierstrassGenericSmoothGroupComparison
public import FLT.Mazur.WeierstrassSmoothBaseGroupHom

/-!
# Original generic kernel multiplication in the integral smooth ambient group

The original generic group law, transported only across the coefficient-product
comparison, projects to actual integral smooth addition. This is the dense-source
identity needed to restrict multiplication to the retained closure.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassDividedDepth

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  (G : CommGrp (Over (Spec (.of K)))) (f : G ⟶ integralCurveGroup _ hΔ)
  [IsClosedImmersion f.hom.hom.hom.left]

local notation "i" => f.hom.hom.hom.left
local notation "t" => genericKernelToClosureSmooth W hΔ i ≫ genericClosureSmoothStructure W i
local notation "j" => i ≫ genericCurveToIntegralSmooth W hΔ

/-- Retain the original generic group product, including its actual coefficient structure. -/
def genericKernelSmoothGroupPairIso : pullback t t ≅ (G.X ⊗ G.X).left :=
  genericClosureSmoothPairIso W hΔ i ≪≫
    pullback.congrHom (Over.w f.hom.hom.hom) (Over.w f.hom.hom.hom)

/-- The group product comparison preserves the original first input. -/
@[reassoc] theorem genericKernelSmoothGroupPairIso_fst :
    (genericKernelSmoothGroupPairIso W hΔ G f).hom ≫ pullback.fst G.X.hom G.X.hom =
      pullback.fst t t := by
  simp only [genericKernelSmoothGroupPairIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  exact genericClosureSmoothPairIso_fst W hΔ i

/-- The group product comparison preserves the original second input. -/
@[reassoc] theorem genericKernelSmoothGroupPairIso_snd :
    (genericKernelSmoothGroupPairIso W hΔ G f).hom ≫ pullback.snd G.X.hom G.X.hom =
      pullback.snd t t := by
  simp only [genericKernelSmoothGroupPairIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  exact genericClosureSmoothPairIso_snd W hΔ i

/-- The original generic inclusion followed by the constructed smooth group comparison. -/
def genericKernelSmoothGroupHom : G ⟶ originalSmoothBaseChangeGroup K W :=
  f ≫ (genericSmoothGroupIso W hΔ).hom

omit [IsFractionRing R K] [IsClosedImmersion f.hom.hom.hom.left] in
/-- The projected group morphism retains the exact original generic inclusion. -/
@[reassoc] theorem genericKernelSmoothGroupHom_fst :
    (genericKernelSmoothGroupHom W hΔ G f).hom.hom.hom.left ≫
      pullback.fst (integralSmoothStructure W)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) = j := by
  change (i ≫ (genericSmoothGroupIso W hΔ).hom.hom.hom.hom.left) ≫ _ = _
  rw [Category.assoc, genericSmoothGroupIso_fst]

/-- The original generic multiplication on the precise source used for integral descent. -/
def genericKernelSmoothPairMultiplication : pullback t t ⟶ G.X.left :=
  (genericKernelSmoothGroupPairIso W hΔ G f).hom ≫ μ[G.X].left

omit [IsFractionRing R K] [IsClosedImmersion f.hom.hom.hom.left] in
/-- The projected original generic inputs have the same integral coefficient. -/
theorem genericKernelSmoothPair_condition :
    (pullback.fst t t ≫ j) ≫ integralSmoothStructure W =
      (pullback.snd t t ≫ j) ≫ integralSmoothStructure W := by
  have hj : j ≫ integralSmoothStructure W = t := by
    rw [← genericKernelToClosureSmooth_inclusion, Category.assoc,
      genericClosureSmoothInclusion_structure]
  rw [Category.assoc, hj, Category.assoc, hj]
  exact pullback.condition

/-- The original generic group product agrees with actual smooth ambient addition. -/
@[reassoc] theorem genericKernelSmoothPairMultiplication_inclusion :
    genericKernelSmoothPairMultiplication W hΔ G f ≫ j =
      pullback.lift (pullback.fst t t ≫ j) (pullback.snd t t ≫ j)
        (genericKernelSmoothPair_condition W hΔ G f) ≫ smoothFactorAddition W := by
  have hm := smoothBaseGroupHom_mul W G (genericKernelSmoothGroupHom W hΔ G f)
  simp only [genericKernelSmoothGroupHom_fst] at hm
  rw [genericKernelSmoothPairMultiplication, Category.assoc, hm, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc,
      genericKernelSmoothGroupPairIso_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
      genericKernelSmoothGroupPairIso_snd]

end FLT.Mazur.WeierstrassIntegralChart

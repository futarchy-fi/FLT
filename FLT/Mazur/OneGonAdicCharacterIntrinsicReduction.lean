/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterSmoothEffectivity

/-!
# Original intrinsic homomorphisms are the effective map's reductions

Equation transport identifies the constructed finite group homomorphisms
with those of the actual coefficient-reduced curve. Their original full
multiplication defects vanish, and so do all reductions of the effective defect.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart WeierstrassDiagonalizableDefect
open DiagonalizableCobar

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] (I : Ideal R) (t : R)
  (ht : t ∈ I) (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- Each constructed stage as a homomorphism into the actual coefficient-reduced original curve. -/
def towerIntrinsicHom (m : ℕ) : stageSource I G m ⟶
    integralSmoothGroup ((equation t).map (algebraMap R (StageRing I m))) :=
  tower I t ht g m ≫ eqToHom (congrArg integralSmoothGroup
    (equation_map t (algebraMap R (StageRing I m))).symm)

/-- The original intrinsic point retains exactly the constructed map and smooth projection. -/
theorem towerIntrinsicPoint_left (m : ℕ) :
    (intrinsicCharacterPoint (equation t) (towerIntrinsicHom I t ht g m)).left =
      (tower I t ht g m).hom.hom.hom.left ≫ smoothProjection I t m := by
  rw [intrinsicCharacterPoint_left]
  change (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
  exact Category.assoc _ _ _

variable [Finite G] [IsAdicComplete I R]

/-- Reduction of the effective original relative point is the original intrinsic stage point. -/
theorem effectiveSmoothOver_reduction (m : ℕ) :
    smoothAlgebraReduction (equation t) (coefficientReduction R G (I ^ (m + 1)))
      (effectiveSmoothOver I t ht g) =
        intrinsicCharacterPoint (equation t) (towerIntrinsicHom I t ht g m) := by
  apply Over.OverMorphism.ext
  rw [towerIntrinsicPoint_left]
  exact effectiveSmooth_reduction I t ht g m

/-- Every full finite reduction of the effective multiplication defect is the identity. -/
theorem effectiveSmoothOver_defect_reduction (m : ℕ) :
    smoothAlgebraReduction (equation t) (coefficientReduction R (G × G) (I ^ (m + 1)))
      (defect (equation t) (effectiveSmoothOver I t ht g)) = 1 := by
  rw [defect_reduction, effectiveSmoothOver_reduction]
  exact intrinsicCharacterPoint_defect (equation t) (towerIntrinsicHom I t ht g m)

end FLT.Mazur.OneGonAdicCharacterTower

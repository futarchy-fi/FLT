/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedOddAdjustedComparison
public import FLT.Mazur.EllipticResolvedEvenAdjustedComparison
import all FLT.Mazur.EllipticResolvedOddAdjustedComparison
import all FLT.Mazur.EllipticResolvedEvenAdjustedComparison

/-!
# Full closed-fiber compatibility of the adjusted arithmetic smooth comparison

The smooth restriction agrees as a morphism into the actual complete closed
fiber product, retaining both its total-space and residue-field projections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp
variable (F : Type) [Field F] (n : ℕ) (hn : 2 ≤ n) [NeZero n]
local notation "p" => exactVeroneseProjToBase F n hn

/-- The original smooth closed fiber includes in the full closed fiber over the same field. -/
def completeClosedSmoothFiberInclusion :
    pullback ((p).smoothLocus.ι ≫ p) (completeClosedBase F) ⟶
      pullback p (completeClosedBase F) :=
  pullback.lift (pullback.fst _ _ ≫ (p).smoothLocus.ι) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

/-- The inclusion retains the actual total-space projection. -/
@[reassoc] theorem completeClosedSmoothFiberInclusion_fst :
    completeClosedSmoothFiberInclusion F n hn ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (p).smoothLocus.ι := pullback.lift_fst _ _ _

/-- The inclusion retains the actual residue-field projection. -/
@[reassoc] theorem completeClosedSmoothFiberInclusion_snd :
    completeClosedSmoothFiberInclusion F n hn ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

end FLT.Mazur.PolygonInfinitesimalStages

namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp
variable {K : Type} [Field K] (A : ValuationSubring K) (s : ℕ)
  {W : WeierstrassCurve A} {π : A}
local notation "F" => ResidueField A

/-- The full odd comparison restricts to the independently constructed complete smooth iso. -/
@[reassoc] theorem resolvedOddAdjustedClosedIso_smooth_square
    (D : SplitNodeDepth W π (2 * s + 3)) (r : (ResidueField A)ˣ) :
    (resolvedSplitStructure A D).smoothLocus.ι ≫ (resolvedOddAdjustedClosedIso A s D r).hom =
      (resolvedCompleteSmoothFiberIso A D r (by omega)).hom ≫
        completeClosedSmoothFiberInclusion F (2 * s + 3) (by omega) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeClosedSmoothFiberInclusion_fst]
    exact resolvedOddAdjustedClosedIso_smooth A s D r
  · simp only [Category.assoc, completeClosedSmoothFiberInclusion_snd,
      resolvedOddAdjustedClosedIso_snd, resolvedCompleteSmoothFiberIso_snd]

/-- The full even comparison has the same exact smooth restriction, including depth two. -/
@[reassoc] theorem resolvedEvenAdjustedClosedIso_smooth_square
    (D : SplitNodeDepth W π (2 * s + 2)) (r : (ResidueField A)ˣ) :
    (resolvedSplitStructure A D).smoothLocus.ι ≫ (resolvedEvenAdjustedClosedIso A s D r).hom =
      (resolvedCompleteSmoothFiberIso A D r (by omega)).hom ≫
        completeClosedSmoothFiberInclusion F (2 * s + 2) (by omega) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeClosedSmoothFiberInclusion_fst]
    exact resolvedEvenAdjustedClosedIso_smooth A s D r
  · simp only [Category.assoc, completeClosedSmoothFiberInclusion_snd,
      resolvedEvenAdjustedClosedIso_snd, resolvedCompleteSmoothFiberIso_snd]

end FLT.Mazur.WeierstrassDividedDepth

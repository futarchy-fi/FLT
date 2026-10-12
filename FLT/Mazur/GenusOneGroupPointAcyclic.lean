/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupPointPowers
public import FLT.Mazur.CurveLineHigherVanishing

/-!
# All positive cohomology of positive point powers vanishes

Combine the genus-one H¹ calculation with dimension-one higher vanishing.
These are the actual point powers, so their vanishing can be used as the
fiber input for relative cohomology and base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg in
/-- Every positive point power is acyclic in all positive degrees. -/
theorem genusOne_group_pointPower_acyclic (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Subsingleton (ModuleH (tensorPower (divisorLineBundle s.left.ker hI) m) (n + 1)) := by
  cases n with
  | zero =>
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    exact genusOne_group_pointPower_h1 G hd hc hg s hI a
  | succ n =>
    obtain ⟨B, hB⟩ := pointedCurve_exists_ample_line G.hom hd.le s.left s.w
    exact curve_line_higher_vanishing G.hom hd.le hB
      (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m) n

end FLT.Mazur.FCurve

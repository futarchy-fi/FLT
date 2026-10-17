/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphFlatExt
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Flat source opens of the original graph project by open immersions

Flatness is required only on the selected source open. The original flat-test
uniqueness proves its projection monic, without assuming flatness of whole fibers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (U : (completeIdentityActionGraphClosure K n h).Opens)
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "q" => U.ι ≫ (p)
variable [Flat (U.ι ≫ completeIdentityActionGraphProjection K n h)]

/-- A flat source-open projection has no distinct graph points over the same original input. -/
theorem completeIdentityGraphFlatSource_mono : Mono (q) := by
  let a := pullback.fst (q) (q)
  let b := pullback.snd (q) (q)
  have he : a ≫ U.ι ≫ (p) = b ≫ U.ι ≫ (p) := pullback.condition
  have hr : a ≫ U.ι = b ≫ U.ι := by
    apply completeIdentityActionGraph_flat_ext K n h (a ≫ (q) ≫ (s) ≫ (π))
    · simp only [Category.assoc]
    · simpa only [Category.assoc] using he
  have hab : a = b := (cancel_mono U.ι).mp hr
  constructor
  intro Z c d hcd
  let k := pullback.lift c d hcd
  calc
    c = k ≫ a := (pullback.lift_fst _ _ _).symm
    _ = k ≫ b := congrArg (k ≫ ·) hab
    _ = d := pullback.lift_snd _ _ _

/-- Flatness on a source open already identifies it with an open of the original input. -/
theorem completeIdentityGraphFlatSource_open : IsOpenImmersion (q) := by
  let _ := completeIdentityGraphFlatSource_mono K n h U
  exact IsOpenImmersion.of_flat_of_mono (q)

end FLT.Mazur.PolygonInfinitesimalStages

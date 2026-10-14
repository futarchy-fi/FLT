/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicFactorization
public import FLT.Mazur.PolygonCompleteCartesianMarkings

/-!
# The original cubic morphism on a specified Cartesian family

Construct the actual base-changed target cubic and its morphism from the given
family. The resulting square with the original cubic morphism is Cartesian;
no replacement of the given family by a chosen categorical pullback is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s) (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "c" => integralCurveStructure (W)

/-- The original cubic with coefficients changed along the specified base morphism. -/
def completePointCubicBaseChange : Scheme := pullback (c) (s ≫ (S₀).toSpecΓ)

/-- The actual comparison from the specified Cartesian family to the changed cubic. -/
def completePointToCubicBaseChange : Y ⟶ completePointCubicBaseChange K n h s i :=
  pullback.lift (p ≫ (g)) q (by
    rw [Category.assoc, completePointToIntegralCubic_over,
      ← Category.assoc, hs.w, Category.assoc])

/-- Projection to the original cubic retains the original comparison morphism. -/
@[reassoc] theorem completePointToCubicBaseChange_fst :
    completePointToCubicBaseChange K n h s p q hs i ≫ pullback.fst _ _ = p ≫ (g) :=
  pullback.lift_fst _ _ _

/-- Projection to the specified base retains its original structural morphism. -/
@[reassoc] theorem completePointToCubicBaseChange_snd :
    completePointToCubicBaseChange K n h s p q hs i ≫ pullback.snd _ _ = q :=
  pullback.lift_snd _ _ _

/-- The new comparison is the actual Cartesian change of the original cubic map. -/
theorem completePointToCubicBaseChange_isPullback :
    IsPullback (completePointToCubicBaseChange K n h s p q hs i) p
      (pullback.fst (c) (s ≫ (S₀).toSpecΓ)) (g) := by
  have H : IsPullback p q ((g) ≫ (c)) (s ≫ (S₀).toSpecΓ) := by
    rw [completePointToIntegralCubic_over]
    exact hs.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (S₀).toSpecΓ)
      (by simp) (by simp) (by simp) (by simp)
  have H' : IsPullback
      (completePointToCubicBaseChange K n h s p q hs i ≫ pullback.snd _ _) p
      (s ≫ (S₀).toSpecΓ) ((g) ≫ (c)) := by
    rw [completePointToCubicBaseChange_snd]
    exact H.flip
  exact H'.of_right (completePointToCubicBaseChange_fst K n h s p q hs i)
    (IsPullback.of_hasPullback (c) (s ≫ (S₀).toSpecΓ)).flip

end FLT.Mazur.PolygonInfinitesimalStages

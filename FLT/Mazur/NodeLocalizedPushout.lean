/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SplitPairPushout
public import FLT.Mazur.NodeLocalDescent

/-!
# Scheme pushouts on saturated principal node neighborhoods

The two genuinely localized branches pinch at their original origins.
This arbitrary-target universal property retains the chosen denominator.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.NodeLocalizedPushout
open PolygonNodeEqualizer PolygonNodePresentation NodeLocalizedEqualizer NodeLocalDescent
set_option backward.isDefEq.respectTransparency false
universe u
variable (K : Type u) [Field K] (s : A (R := K)) (hs : aEval s = 1)

/-- The first branch evaluation retains its constant section. -/
theorem first_section : (evalFirst s hs).comp
    ((algebraMap K[X] (Localization.Away (first s))).comp C) = RingHom.id K := by
  ext k
  change evaluation (first s) 0 (first_value s hs) (algebraMap K[X] _ (C k)) = k
  rw [evaluation_algebraMap, eval_C]

/-- The second branch evaluation retains its constant section. -/
theorem second_section : (evalSecond s hs).comp
    ((algebraMap K[X] (Localization.Away (second s))).comp C) = RingHom.id K := by
  ext k
  change evaluation (second s) 0 (second_value s hs) (algebraMap K[X] _ (C k)) = k
  rw [evaluation_algebraMap, eval_C]

/-- Pinching the original localized branches gives a scheme pushout. -/
theorem isPushout : IsPushout (firstOrigin K s hs) (secondOrigin K s hs)
    (firstBranch K s hs) (secondBranch K s hs) :=
  SplitPairEqualizer.isPushout (evalFirst s hs) (evalSecond s hs)
    ((algebraMap K[X] (Localization.Away (first s))).comp C)
    ((algebraMap K[X] (Localization.Away (second s))).comp C)
    (first_section K s hs) (second_section K s hs)

/-- The full local universal property transports to the specified original chart. -/
theorem isPushout_of_iso {X : Scheme.{u}} (e : Spec (.of (E s hs)) ≅ X) :
    IsPushout (firstOrigin K s hs) (secondOrigin K s hs)
      (firstBranch K s hs ≫ e.hom) (secondBranch K s hs ≫ e.hom) :=
  (isPushout K s hs).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    (by simp) (by simp) (by simp) (by simp)

end FLT.Mazur.NodeLocalizedPushout

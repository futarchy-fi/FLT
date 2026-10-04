/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerCanonicalSection
public import FLT.Mazur.PolygonCanonicalSection
/-!
# Canonical sections for the original polygon power comparison

The tensor-based component comparison preserves canonical sections in every
power, using preservation by the original divisor-power isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonDivisorLineComparison
open PolygonPinching PolygonDivisorNormalizationPullback FCurve
open ModuleLineBundleTensorPullback
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- The original component comparison preserves the actual powered canonical section. -/
lemma linePowerIso_canonical (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    (linePowerIso K n hn p q h a i m).hom.app ⊤
      (pullGlobal (componentι K n i ≫ p).left _
        (divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m) ⊤)) =
    divisorSection ((ProjectiveLineMarkedCharts.relativeCartier K (a i)).1.pow m) ⊤ := by
  rw [linePowerIso, sectionIso_trans, sectionIso_trans, sectionIso_trans]
  change (divisorLineBundlePowerIso _ m).hom.app ⊤
    ((divisorTensorPowerCongr _ m).hom.app ⊤
      ((tensorPowerIso _ _ m).hom.app ⊤
        (((Scheme.Modules.pullback _).map (divisorLineBundlePowerIso _ m).inv).app ⊤
          (pullGlobal _ _ _)))) = _
  rw [pullGlobal_naturality, sectionIso_inv_of_eq _ _ _ _ (divisorSection_power _ ⊤ m)]
  rw [tensorPowerSection_pullback, tensorPowerSection_congr, lineIso_canonical,
    divisorSection_power]
end FLT.Mazur.PolygonDivisorLineComparison

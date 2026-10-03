/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionMap
public import FLT.Mazur.PolygonDivisorLinePowerPullback
/-!
# Canonical sections on polygon normalization components

The existing degree-one comparison preserves the global canonical section,
and the existing tensor-power congruence preserves arbitrary pure powers.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}}
open ModuleLineBundleTensorPullback
/-- The existing divisor tensor-power congruence preserves pure powers of sections. -/
lemma tensorPowerSection_congr {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(M, U)) (m : ℕ) :
    (divisorTensorPowerCongr e m).hom.app U (tensorPowerSection M U s m) =
      tensorPowerSection N U (e.hom.app U s) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (ModuleSheafTensor.congr e (divisorTensorPowerCongr e m)).hom.app U
      (ModuleSheafTensor.pure _ _ U s (tensorPowerSection M U s m)) = _
    rw [sectionTensor_congr, ih]
    rfl
end FLT.Mazur.FCurve

namespace FLT.Mazur.PolygonDivisorLineComparison
open PolygonPinching PolygonDivisorNormalizationPullback FCurve
open ModuleLineBundleTensorPullback
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- The degree-one polygon comparison preserves the actual global canonical section. -/
lemma lineIso_canonical (a : Fin n → Kˣ) (i : Fin n) :
    (lineIso K n hn p q h a i).hom.app ⊤
      (pullGlobal (componentι K n i ≫ p).left _
        (divisorSection (PolygonBoundaryDivisor.cartier K n p hn q h a).1 ⊤)) =
    divisorSection (ProjectiveLineMarkedCharts.relativeCartier K (a i)).1 ⊤ :=
  pullGlobal_section_map (componentι K n i ≫ p).left
    (divisorSectionMap (PolygonBoundaryDivisor.cartier K n p hn q h a).1)
    (divisorSectionMap (ProjectiveLineMarkedCharts.relativeCartier K (a i)).1)
    (lineIso K n hn p q h a i).hom (lineIso_section K n hn p q h a i)
/-- Pullback and tensor congruence preserve powered canonical sections on components. -/
lemma lineTensorPower_canonical (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    (tensorPowerIso (componentι K n i ≫ p).left _ m ≪≫
      divisorTensorPowerCongr (lineIso K n hn p q h a i) m).hom.app ⊤
        (pullGlobal (componentι K n i ≫ p).left _
          (tensorPowerSection _ ⊤
            (divisorSection (PolygonBoundaryDivisor.cartier K n p hn q h a).1 ⊤) m)) =
      tensorPowerSection _ ⊤
        (divisorSection (ProjectiveLineMarkedCharts.relativeCartier K (a i)).1 ⊤) m := by
  rw [sectionIso_trans, tensorPowerSection_pullback, tensorPowerSection_congr,
    lineIso_canonical]
end FLT.Mazur.PolygonDivisorLineComparison

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionBaseChangeLine
public import FLT.Mazur.TensorPowerPullbackSquare
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# All tensor degrees of the original family contraction comparison

Every tensor power of the actual marking line retains its canonical section
and its base-change square, including the structure module in degree zero.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching FCurve
open PolygonMarkingBaseChange hiding markingLineIso markingLineIso_section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] contraction baseChangedContraction tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)
  {T : Scheme} (g : T ⟶ Spec (.of K)) (a : Kˣ) (d : ℕ)

/-- The family contraction preserves every tensor power of the original marking section. -/
theorem baseChangedMarkingLineIso_power_section :
    DivisorLinePowerSectionCompatible (baseChangedContraction K n hn p q h i g).left
      (markingIdeal_cartier K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) g a 0).1
      (markingIdeal_cartier K n hn p q h g a i).1
      (baseChangedMarkingLineIso K n hn p q h i g a) d :=
  (baseChangedMarkingLineIso_section K n hn p q h i g a).tensorPower_section d

/-- Base change and descended contraction commute on every actual tensor-power comparison. -/
theorem baseChangedMarkingLineIso_power_square :
    LinePullbackSquare (baseChangedContraction K n hn p q h i g).left
      (pullback.fst (PolygonAtlas.polygon K 1).hom g) (pullback.fst C.hom g)
      (contraction K n hn p q h i).left (baseChangedContraction_square K n hn p q h i g).w
      (tensorPowerPullbackComparison _
        (PolygonMarkingBaseChange.markingLineIso K 1 (by decide)
          (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
          (PolygonAtlas.isPushout K 1 (by decide)) g a 0) d)
      (tensorPowerPullbackComparison _ (baseChangedMarkingLineIso K n hn p q h i g a) d)
      (tensorPowerPullbackComparison _ (markingLineIso K n hn p q h i a) d)
      (tensorPowerPullbackComparison _
        (PolygonMarkingBaseChange.markingLineIso K n hn p q h g a i) d) :=
  (baseChangedMarkingLineIso_square K n hn p q h i g a).tensorPower d

end FLT.Mazur.PolygonOneGonContraction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCartierIdealPullback
public import FLT.Mazur.DivisorLinePullback
public import FLT.Mazur.RelativeVeryAmpleLineBundle

/-!
# Relative Cartier divisor line bundles under arbitrary base change

The actual ideal comparison gives the positive divisor line isomorphism,
preserving its canonical section. All tensor powers are transported too.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback ProjectiveSpace
variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
  (I : X.IdealSheafData) (hI : RelativeEffectiveCartier f I)

/-- Canonical comparison of positive divisor sheaves for any base map. -/
def relativeCartierDivisorPullbackIso :
    (Scheme.Modules.pullback (pullback.fst f g)).obj (divisorLineBundle I hI.1) ≅
      divisorLineBundle (I.comap (pullback.fst f g)) (relativeCartierBaseChange f g I hI).1 := by
  let := relativeCartierIdealPullback f g I hI
  exact divisorLinePullbackIsoOfEq _ hI.1 (relativeCartierBaseChange f g I hI).1 rfl

/-- The comparison preserves the canonical section morphism. -/
@[reassoc]
lemma relativeCartierDivisorPullbackIso_section :
    (Scheme.Modules.pullback (pullback.fst f g)).map (divisorSectionMap hI.1) ≫
      (relativeCartierDivisorPullbackIso f g I hI).hom =
    (modulePullbackUnitIso (pullback.fst f g)).hom ≫
      divisorSectionMap (relativeCartierBaseChange f g I hI).1 := by
  let := relativeCartierIdealPullback f g I hI
  exact divisorLinePullbackIsoOfEq_section _ hI.1 (relativeCartierBaseChange f g I hI).1 rfl

/-- Positive and zero tensor powers commute with arbitrary relative Cartier base change. -/
def relativeCartierDivisorPowerPullbackIso (m : ℕ) :
    (Scheme.Modules.pullback (pullback.fst f g)).obj (tensorPower (divisorLineBundle I hI.1) m) ≅
      tensorPower (divisorLineBundle (I.comap (pullback.fst f g))
        (relativeCartierBaseChange f g I hI).1) m :=
  tensorPowerIso _ _ m ≪≫ tensorPowerCongr (relativeCartierDivisorPullbackIso f g I hI) m

/-- The power-zero comparison is the canonical structure-module comparison. -/
@[simp]
lemma relativeCartierDivisorPowerPullbackIso_zero :
    relativeCartierDivisorPowerPullbackIso f g I hI 0 =
      modulePullbackUnitIso (pullback.fst f g) := by
  simp [relativeCartierDivisorPowerPullbackIso, tensorPowerIso, tensorPowerCongr]

end FLT.Mazur.FCurve

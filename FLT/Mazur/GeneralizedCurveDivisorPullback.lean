/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCartierStalks
public import FLT.Mazur.RelativeCartierDivisorPullback

/-!
# Actual subgroup divisor sheaves under arbitrary base change

Once the subgroup ideal is Cartier, its unconditional flatness proves invertibility of
the canonical ideal comparison. The general divisor-line and tensor-power
comparisons in RelativeCartierDivisorPullback then apply to its comap ideal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open FCurve FCurve.ModuleLineBundleTensorPullback
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} (H : E.FiniteSubgroup n)

/-- A Cartier subgroup ideal stays Cartier under every base change. -/
theorem effectiveCartier_baseChange (hI : EffectiveCartier H.ideal) (g : T ⟶ S) :
    EffectiveCartier (H.baseChange g).ideal := by
  rw [baseChange_ideal]
  exact (relativeCartierBaseChange E.curve.hom g H.ideal ⟨hI, inferInstance⟩).1

/-- Canonical ideal comparison for the actual subgroup divisor. -/
theorem idealPullbackHom_isIso (hI : EffectiveCartier H.ideal) (g : T ⟶ S) :
    IsIso (idealModulePullbackHom H.ideal (pullback.fst E.curve.hom g)) :=
  relativeCartierIdealPullback E.curve.hom g H.ideal ⟨hI, inferInstance⟩


end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackTowerExt
public import FLT.Mazur.GeneralizedCurveBaseChangeTowerMap

/-!
# Original projections of full generalized-curve towers

The full curve tower comparison preserves the original curve projection.
This formula permits proofs without unfolding its categorical construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve

/-- The full curve comparison retains the original projection through both pullbacks. -/
@[reassoc] theorem baseChangeCompEqIso_curve_fst_fst {S T U : Scheme}
    (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (h : U ⟶ T) (k : U ⟶ S)
    (w : h ≫ g = k) :
    (E.baseChangeCompEqIso g h k w.symm).hom.curve.left ≫
      Limits.pullback.fst (Limits.pullback.snd E.curve.hom g) h ≫
        Limits.pullback.fst E.curve.hom g = Limits.pullback.fst E.curve.hom k := by
  rw [baseChangeCompEqIso_curve_tower E g h k w]
  exact OverPullbackCoherence.towerIso_fst_fst g h k w E.curve

end FLT.Mazur.GeneralizedEllipticCurve

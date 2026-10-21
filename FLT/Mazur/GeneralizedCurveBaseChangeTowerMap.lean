/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackSealedTower
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Underlying maps of full generalized-curve tower comparisons

The actual generalized-curve comparison induces the canonical over-category
tower morphism, including its opaque interface.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve

/-- The full curve tower comparison has the canonical underlying over-category map. -/
theorem baseChangeCompEqIso_curve_tower {S T U : Scheme} (E : GeneralizedEllipticCurve S)
    (g : T ⟶ S) (h : U ⟶ T) (k : U ⟶ S) (w : h ≫ g = k) :
    (E.baseChangeCompEqIso g h k w.symm).hom.curve =
      ((OverPullbackCoherence.towerIso g h k w).app E.curve).hom := by
  subst k
  rfl

/-- The full curve comparison equals the opaque canonical tower morphism. -/
theorem baseChangeCompEqIso_curve_towerMap {S T U : Scheme}
    (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (h : U ⟶ T) (k : U ⟶ S)
    (w : h ≫ g = k) :
    (E.baseChangeCompEqIso g h k w.symm).hom.curve =
      OverPullbackCoherence.towerMap g h k w E.curve := by
  rw [OverPullbackCoherence.towerMap_def]
  exact baseChangeCompEqIso_curve_tower E g h k w

end FLT.Mazur.GeneralizedEllipticCurve

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionModel
public import FLT.EllipticCurve.CubicClassicalReduction
public import FLT.EllipticCurve.NTorsionFinite

/-! # Field-valued points of the represented torsion kernel -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- The represented torsion kernel has exactly the classical torsion points
over every field algebra, in every characteristic. -/
def classicalTorsionPointEquiv (K : Type u) [Field K] [Algebra R K]
    [DecidableEq K] (n : ℕ) :
    (pointSource (R := R) K ⟶ torsionModel W n) ≃
      {P : (W.map (algebraMap R K)).toAffine.Point // n • P = 0} :=
  (torsionModelPointEquiv W n (pointSource K)).trans
    { toFun := fun f => ⟨((classicalPointEquiv W K).symm f.1).toAdd, by
        change ((classicalPointEquiv W K).symm f.1) ^ n = 1
        rw [← map_pow, f.2, map_one]⟩
      invFun := fun P => ⟨classicalPointEquiv W K (Multiplicative.ofAdd P.1), by
        rw [← map_pow]
        have h : Multiplicative.ofAdd P.1 ^ n = 1 := congrArg Multiplicative.ofAdd P.2
        rw [h, map_one]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        exact (classicalPointEquiv W K).apply_symm_apply f.1
      right_inv := by
        intro P
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd
          ((classicalPointEquiv W K).symm_apply_apply (Multiplicative.ofAdd P.1)) }

/-- Nonzero-order torsion has finitely many scheme-valued points over every field. -/
theorem finite_torsionModel_fieldPoints (K : Type u) [Field K] [Algebra R K]
    {n : ℕ} (hn : n ≠ 0) :
    Finite (pointSource (R := R) K ⟶ torsionModel W n) := by
  classical
  let : Finite {P : (W.map (algebraMap R K)).toAffine.Point // n • P = 0} :=
    ((W.map (algebraMap R K)).toAffine.finite_setOf_nsmul_eq_zero
      (Nat.pos_of_ne_zero hn)).to_subtype
  exact Finite.of_equiv _ (classicalTorsionPointEquiv W K n).symm

end WeierstrassCurve.CubicCharts

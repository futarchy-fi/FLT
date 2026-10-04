/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleUniversalCover
public import FLT.GroupScheme.PDivisibleTateAction
public import FLT.GroupScheme.RaynaudGeometricIntegralPoints

/-! # Original Tate vectors as integral inverse-p sequences -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K S : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing S] [Algebra R S]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- Each original Tate coordinate specializes from its unique integral extension. -/
def integralTateColimitAt (c : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    (x : X.tateSequences) (n : ℕ) : X.PointColimit S :=
  X.pointColimitMk n (c.comp ((X.level n).integralPointCoordinate (X.tateEval n x)))

/-- The original Tate reduction becomes actual p multiplication in the point colimit. -/
theorem integralTateColimitAt_transition
    (c : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (x : X.tateSequences) (n : ℕ) :
    X.pointColimitMul p (X.integralTateColimitAt c x (n + 1)) =
      X.integralTateColimitAt c x n := by
  let z := (X.level (n + 1)).integralPointCoordinate (X.tateEval (n + 1) x)
  have he : ((X.level (n + 1)).multiply p).toAlgHom =
      (X.reduction (Nat.le_succ n)).toAlgHom.comp (X.inclusion (Nat.le_succ n)).toAlgHom := by
    have h := X.reduction_inclusion (Nat.le_succ n)
    rw [show n.succ - n = 1 by omega, pow_one] at h
    ext a
    exact (DFunLike.congr_fun h a).symm
  have hz : z.comp (X.reduction (Nat.le_succ n)).toAlgHom =
      (X.level n).integralPointCoordinate (X.tateEval n x) := by
    rw [← ModelHom.integralPointCoordinate_genericHom, X.tateEval_reduction]
  change X.pointColimitMk (n + 1)
    ((c.comp z).comp ((X.level (n + 1)).multiply p).toAlgHom) = _
  rw [he, ← AlgHom.comp_assoc, AlgHom.comp_assoc c z, hz]
  exact X.pointColimitMk_inclusion _ _

/-- The specified original Tate vector defines an actual integral inverse-p sequence. -/
def integralTateCover (c : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    (x : X.tateSequences) : X.UniversalCover S :=
  ⟨X.integralTateColimitAt c x, X.integralTateColimitAt_transition c x⟩

/-- Integral specialization remains natural on all coordinates at once. -/
theorem integralTateCover_natural {T : Type} [CommRing T] [Algebra R T]
    (c : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (q : S →ₐ[R] T)
    (x : X.tateSequences) :
    X.universalCoverMap q (X.integralTateCover c x) = X.integralTateCover (q.comp c) x := by
  apply Subtype.ext
  funext n
  rfl

end ThreeAdicPlan.PDivisibleSystem

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleIntegralTateCover
public import FLT.GroupScheme.PDivisibleInfinitesimalColimit
public import FLT.GroupScheme.RaynaudIntegralPointAddition

/-! # The zeroth coordinate of a lifted Tate sequence is infinitesimal -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The original Tate coordinate at level zero is the augmentation point after specialization. -/
theorem integralTateCover_zero (c : integralClosure R (AlgebraicClosure K) →ₐ[R] C)
    (x : X.tateSequences) :
    (X.integralTateCover c x).val 0 = X.pointColimitMk 0 (X.levelAugmentation 0) := by
  have hx : X.tateEval 0 x = 0 := by simpa using X.killed 0 (X.tateEval 0 x)
  change X.pointColimitMk 0 (c.comp ((X.level 0).integralPointCoordinate (X.tateEval 0 x))) = _
  rw [hx, FF.integralPointCoordinate_zero]
  apply congrArg (X.pointColimitMk 0)
  ext a
  change c (algebraMap R _ (Coalgebra.counit a)) = algebraMap R C (Coalgebra.counit a)
  exact c.commutes _

/-- The zeroth coordinate of any genuine simultaneous Tate lift lies in the actual kernel. -/
def liftedTateInfinitesimal (q : B →ₐ[R] C)
    (c : integralClosure R (AlgebraicClosure K) →ₐ[R] C) (x : X.tateSequences)
    (y : X.UniversalCover B) (hy : X.universalCoverMap q y = X.integralTateCover c x) :
    X.InfinitesimalColimit q :=
  ⟨y.val 0, (congrArg (fun z : X.UniversalCover C ↦ z.val 0) hy).trans
    (X.integralTateCover_zero c x)⟩

end ThreeAdicPlan.PDivisibleSystem

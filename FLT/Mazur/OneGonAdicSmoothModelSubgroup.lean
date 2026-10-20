/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothModelHom

/-!
# The actual canonical subgroup over finite coefficients

The constructed closed factor and its proved group law form a rank-n finite
subgroup. Its entire curve ideal and original complete-base recovery are retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace FLT.Mazur.OneGonAdicCharacterTower

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The same enlarged character source, now bundled with its proved smooth homomorphism. -/
def smoothModelFiniteSubgroup : (smoothModelCurve I t ht n).FiniteSubgroup n where
  carrier := smoothModelCarrier I t ht n
  commGroup := by
    let _ : CommGrpObj (algebraicCarrier I t ht n) :=
      RootsOfUnityScheme.commGrpObj (algebraicBase I t ht n) n
    let K := (Over.pullback (smoothModelBaseMap I t ht n)).mapCommGrp.obj
      (CommGrp.mk (algebraicCarrier I t ht n))
    exact { toGrpObj := K.grp, toIsCommMonObj := K.comm }
  inclusion := smoothModelFactor I t ht n
  degree := smoothModelCarrier_degree I t ht n

/-- Its whole-curve map is precisely the already constructed finite coefficient embedding. -/
theorem smoothModelFiniteSubgroup_curveMap :
    (smoothModelFiniteSubgroup I t ht n).curveMap = smoothModelEmbedding I t ht n :=
  smoothModelFactor_inclusion I t ht n

/-- Its entire ideal retains the original finite coefficient ideal under enlargement. -/
theorem smoothModelFiniteSubgroup_ideal :
    (smoothModelFiniteSubgroup I t ht n).ideal =
      (algebraicEmbedding I t ht n).ker.comap
        (pullback.fst (algebraicCurve I t ht n).curve.hom (smoothModelBaseMap I t ht n)) := by
  change (smoothModelFiniteSubgroup I t ht n).curveMap.left.ker = _
  rw [smoothModelFiniteSubgroup_curveMap, smoothModelEmbedding_ideal]

/-- Recovery retains the actual canonical subgroup embedding, not just its support. -/
theorem smoothModelFiniteSubgroup_recovery_isPullback :
    IsPullback (smoothModelSourceRecovery I t ht n)
      (canonicalFiniteSubgroup I t ht n).curveMap.left
      (smoothModelFiniteSubgroup I t ht n).curveMap.left
      (smoothModelCurveRecovery I t ht n) := by
  rw [smoothModelFiniteSubgroup_curveMap]
  exact smoothModelEmbedding_recovery_isPullback I t ht n

/-- Recovery retains the full canonical ideal, including infinitesimal multiplicities. -/
theorem smoothModelFiniteSubgroup_recovery_ideal :
    (canonicalFiniteSubgroup I t ht n).ideal =
      (smoothModelFiniteSubgroup I t ht n).ideal.comap (smoothModelCurveRecovery I t ht n) := by
  change _ = (smoothModelFiniteSubgroup I t ht n).curveMap.left.ker.comap _
  rw [smoothModelFiniteSubgroup_curveMap]
  exact smoothModelEmbedding_recovery_ideal I t ht n

end FLT.Mazur.OneGonAdicCharacterTower

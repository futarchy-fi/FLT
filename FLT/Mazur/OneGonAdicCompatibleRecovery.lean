/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicFullSubgroupRecovery
public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Compatible recovery of the actual finite arithmetic subgroup

The constructed curve and character-source recoveries form a compatible
isomorphism of finite subgroup data. It identifies full ideals and preserves
Cartier generators, including nonreduced subgroup structure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OneGonAdicCharacterTower
open CharacterSchemeBaseChange GeneralizedEllipticCurve FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]
local notation "q" => baseMap (smoothModelBase I t ht n) R

instance smoothModelFullSourceIso_isMonHom :
    IsMonHom (smoothModelFullSourceIso I t ht n).hom := by
  change IsMonHom ((overIso (smoothModelBase I t ht n) R (ZMod n)).hom ≫
    (Over.pullback q).map (smoothModelCharacterIso I t ht n).hom)
  infer_instance

/-- The actual canonical subgroup is the recovery of the finite smooth-stage subgroup. -/
def smoothModelCompatibleRecovery : CompatibleIso (canonicalFiniteSubgroup I t ht n)
    ((smoothModelFiniteSubgroup I t ht n).baseChange q) where
  curve := smoothModelGeneralizedRecoveryIso I t ht n
  subgroup := smoothModelFullSourceIso I t ht n
  compatible := by
    rw [baseChange_curveMap, smoothModelFiniteSubgroup_curveMap]
    exact (smoothModel_full_embedding_recovery I t ht n).symm

/-- Full recovery transports the entire canonical ideal by the inverse curve isomorphism. -/
theorem smoothModelCompatibleRecovery_ideal :
    ((smoothModelFiniteSubgroup I t ht n).baseChange q).ideal =
      (canonicalFiniteSubgroup I t ht n).ideal.comap
        (smoothModelGeneralizedRecoveryIso I t ht n).inv.curve.left :=
  ideal_transport _ _ (smoothModelCompatibleRecovery I t ht n).curve
    (smoothModelCompatibleRecovery I t ht n).subgroup
    (smoothModelCompatibleRecovery I t ht n).compatible

/-- Cartier generators exist on the actual canonical subgroup exactly when they do on recovery. -/
theorem smoothModelCompatibleRecovery_generators :
    (∃ P, (canonicalFiniteSubgroup I t ht n).IsCartierGenerator P) ↔
      ∃ Q, ((smoothModelFiniteSubgroup I t ht n).baseChange q).IsCartierGenerator Q :=
  exists_generator_iff _ _ (smoothModelCompatibleRecovery I t ht n).curve
    (smoothModelCompatibleRecovery I t ht n).subgroup
    (smoothModelCompatibleRecovery I t ht n).compatible

end FLT.Mazur.OneGonAdicCharacterTower

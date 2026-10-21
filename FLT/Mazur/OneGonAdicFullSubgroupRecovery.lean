/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicGeneralizedRecovery
public import FLT.Mazur.OneGonAdicSmoothModelSubgroup

/-!
# Actual subgroup recovery with the full generalized-curve comparison

The canonical subgroup and the finite smooth-stage embedding give the same
whole-cubic morphism under the constructed source and full curve recovery
isomorphisms. Monicity of the smooth inclusion then recovers the subgroup map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower
open CharacterSchemeBaseChange GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]
local notation "q" => baseMap (smoothModelBase I t ht n) R

/-- The original character source is the actual recovery of the enlarged carrier. -/
def smoothModelFullSourceIso : model R (ZMod n) ≅
    (Over.pullback q).obj (smoothModelCarrier I t ht n) :=
  overIso (smoothModelBase I t ht n) R (ZMod n) ≪≫
    (Over.pullback q).mapIso (smoothModelCharacterIso I t ht n)

/-- The source isomorphism retains the previously constructed canonical source projection. -/
@[reassoc] theorem smoothModelFullSourceIso_fst :
    (smoothModelFullSourceIso I t ht n).hom.left ≫
      pullback.fst (smoothModelCarrier I t ht n).hom q =
        smoothModelSourceRecovery I t ht n := by
  change (_ ≫ ((Over.pullback q).map (smoothModelCharacterIso I t ht n).hom).left) ≫ _ = _
  simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc, overIso_fst, smoothModelCharacterIso_recovery]

/-- The constructed recovery maps identify the entire original canonical embedding. -/
theorem smoothModel_full_embedding_recovery :
    (smoothModelFullSourceIso I t ht n).hom ≫
      (Over.pullback q).map (smoothModelEmbedding I t ht n) =
        (canonicalFiniteSubgroup I t ht n).curveMap ≫
          (smoothModelGeneralizedRecoveryIso I t ht n).hom.curve := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc, smoothModelFullSourceIso_fst,
      smoothModelGeneralizedRecoveryIso_fst]
    exact smoothModelEmbedding_recovery I t ht n
  · exact (Over.w _).trans (Over.w _).symm

/-- Full-curve recovery also identifies the original canonical smooth-subgroup map. -/
theorem smoothModel_full_subgroup_recovery :
    (smoothModelFullSourceIso I t ht n).hom ≫
      (Over.pullback q).map (smoothModelFactor I t ht n) =
        (canonicalFiniteSubgroup I t ht n).inclusion ≫
          (smoothModelGeneralizedRecoveryIso I t ht n).hom.group := by
  let E := (smoothModelCurve I t ht n).baseChange q
  have : Mono E.inclusion := by
    dsimp [GeneralizedEllipticCurve.inclusion, curveSmoothInclusion]
    infer_instance
  apply (cancel_mono E.inclusion).mp
  calc
    ((smoothModelFullSourceIso I t ht n).hom ≫
        (Over.pullback q).map (smoothModelFactor I t ht n)) ≫ E.inclusion =
      (smoothModelFullSourceIso I t ht n).hom ≫ (Over.pullback q).map
        (smoothModelFactor I t ht n ≫ (smoothModelCurve I t ht n).inclusion) := by
          rw [Category.assoc, show E.inclusion =
            (Over.pullback q).map (smoothModelCurve I t ht n).inclusion
              from baseChange_inclusion _ _, Functor.map_comp]
    _ = (smoothModelFullSourceIso I t ht n).hom ≫
        (Over.pullback q).map (smoothModelEmbedding I t ht n) := by
          rw [smoothModelFactor_inclusion]
    _ = (canonicalFiniteSubgroup I t ht n).curveMap ≫
        (smoothModelGeneralizedRecoveryIso I t ht n).hom.curve :=
          smoothModel_full_embedding_recovery I t ht n
    _ = _ := by
      change (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _
      rw [Category.assoc, Category.assoc,
        (smoothModelGeneralizedRecoveryIso I t ht n).hom.inclusion]

end FLT.Mazur.OneGonAdicCharacterTower

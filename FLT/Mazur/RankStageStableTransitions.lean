/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantIsomorphismRestriction
public import FLT.Mazur.RankStageGlobalKernelLocalization

/-!
# Actual rank-order isomorphisms when defining ideal powers agree

Equality of the full defining ideals identifies sources, entire relations,
affine cores and full original boundaries. This supplies geometric stable
tail hypotheses without asserting an annihilation conclusion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem inclusion_isIso_of_eq {X : Scheme.{0}} {I J : X.IdealSheafData}
    (h : I ≤ J) (he : I = J) : IsIso (Scheme.IdealSheafData.inclusion h) := by
  subst J
  rw [Scheme.IdealSheafData.inclusion_id]
  infer_instance

private theorem resLE_isIso_of_eq {X Y : Scheme.{0}} (g : X ⟶ Y) [IsIso g]
    (U : Y.Opens) (V : X.Opens) (h : V = g ⁻¹ᵁ U) : IsIso (g.resLE U V h.le) := by
  subst V
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict g U).isIso_fst_of_isIso

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance stableOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance stableOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance stableOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) {k l : ℕ} (h : k ≤ l)
  (he : rankStratumIdeal (Over.mk p) n ^ (l + 1) =
    rankStratumIdeal (Over.mk p) n ^ (k + 1))

include he in
omit [IsAffine A] [LocallyQuasiFinite p] [QuasiCompact p] [IsLocallyNoetherian A] in
/-- Equality of full ideal powers makes the actual closed order transition an isomorphism. -/
theorem rankStageTransition_isIso_of_power_eq :
    IsIso (rankStageTransition (Over.mk p) n h) :=
  inclusion_isIso_of_eq _ he

include he in
omit [IsAffine A] [LocallyQuasiFinite p] in
/-- Stable source orders identify full invariant coefficient rings, even on nonaffine stages. -/
theorem rankStageInvariantTransition_bijective_of_power_eq :
    Function.Bijective (rankStageInvariantTransition e n h) := by
  let _ := rankStageTransition_isIso_of_power_eq n h he
  let _ := (rankStageRelationTransition_isPullback (p := p) n h).isIso_fst_of_isIso
  exact relationPullback_bijective_of_isIso _ _ _ _ _ _ _ _

variable (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)

include he in
/-- The same stable order map identifies the named full affine cores. -/
theorem rankStageCoreMap_isIso_of_power_eq : IsIso (rankStageCoreMap e n a ha h) := by
  let _ := rankStageTransition_isIso_of_power_eq n h he
  exact resLE_isIso_of_eq _ _ _ (rankStageCore_preimage e n a ha h).symm

include he in
/-- Full core coefficients are detected at the stable order. -/
theorem rankStageCoreRestriction_injective_of_power_eq :
    Function.Injective (rankStageCoreRestriction e n a ha h) := by
  let _ := rankStageCoreMap_isIso_of_power_eq e n h he a ha
  intro v w hv
  apply Subtype.ext
  exact appTop_injective (rankStageCoreMap e n a ha h) (congrArg Subtype.val hv)

include he in
omit [IsAffine A] [LocallyQuasiFinite p] in
/-- The whole original homogeneous boundary ideal is reflected at a stable order. -/
theorem rankStageGlobalBoundaryKernel_reflect_of_power_eq (J : A.IdealSheafData)
    (w : rankStageInvariants e n l) :
    rankStageInvariantTransition e n h w ∈ rankStageGlobalBoundaryKernel e n J k ↔
      w ∈ rankStageGlobalBoundaryKernel e n J l := by
  let _ := rankStageTransition_isIso_of_power_eq n h he
  rw [mem_rankStageGlobalBoundaryKernel, mem_rankStageGlobalBoundaryKernel]
  rw [rankStageInvariantTransition_val]
  exact IdealSheafClosedTransitions.section_zero_iff_of_isIso _ _ _
    (rankStageBoundaryIdeal_transition n h J) w.val

end FLT.Mazur.EquivalenceRelationOrderedFrames

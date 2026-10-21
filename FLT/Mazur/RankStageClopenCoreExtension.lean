/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantClopenSectionExtension
public import FLT.Mazur.RankStageCompatibleKernelObstruction
public import FLT.Mazur.RankStageTransitionTopology

/-!
# Compatible extension from clopen rank cores without stable ideal powers

Closedness of a core at order zero propagates through every ideal-power
thickening. Extension by zero then gives full global invariants with ordinary
compatibility and the same full homogeneous boundary values. Higher-rank
points may still accumulate on the rank support in its ambient open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeClopenSectionExtension
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance clopenCoreOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance clopenCoreOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance clopenCoreOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (hclosed : IsClosed (rankStageCore e n a ha 0 : Set (rankThickening (Over.mk p) n 0)))
local notation "U" k:max => rankStageCore e n a ha k
attribute [local irreducible] rankStageCore rankStageInvariantTransition
  rankStageGlobalCoreRestriction rankStageCoreRestriction

include hclosed in
/-- Closedness of the actual core is independent of the nilpotent order. -/
theorem rankStageCore_isClosed_of_zero (k : ℕ) :
    IsClosed (U k : Set (rankThickening (Over.mk p) n k)) := by
  let g := rankStageTransition (Over.mk p) n (Nat.zero_le k)
  apply (g.isClosedEmbedding.isClosed_iff_preimage_isClosed (by
    rw [Set.range_eq_univ.mpr (rankStageTransition_surjective n (Nat.zero_le k))]
    exact Set.subset_univ _)).mpr
  change IsClosed (g ⁻¹ᵁ U k : Set (rankThickening (Over.mk p) n 0))
  rw [rankStageCore_preimage]
  exact hclosed

local notation "hc" k:max => rankStageCore_isClosed_of_zero e n a ha hclosed k
local notation "V" k:max => complement (U k) (hc k)

/-- Extend each full invariant core coefficient by zero on the exact rank support complement. -/
def rankStageClopenCoreExtension (k : ℕ) (v : rankStageCoreInvariants e n a ha k) :
    rankStageInvariants e n k :=
  InvariantClopenSectionExtension.extension _ _ (U k)
    (rankStageCore_invariant e n a ha k) (hc k) v

/-- The full core restriction is a left inverse to the constructed extension. -/
theorem rankStageClopenCoreExtension_restrict (k : ℕ)
    (v : rankStageCoreInvariants e n a ha k) :
    rankStageGlobalCoreRestriction e n a ha k
      (rankStageClopenCoreExtension e n a ha hclosed k v) = v :=
  by
    unfold rankStageGlobalCoreRestriction rankStageClopenCoreExtension
    exact InvariantClopenSectionExtension.restriction_extension _ _ _ _ _ v

/-- Extension preserves the unchanged full original boundary kernel. -/
theorem rankStageClopenCoreExtension_boundary (J : A.IdealSheafData) (k : ℕ)
    (v : rankStageCoreInvariants e n a ha k)
    (hv : (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop v.val = 0) :
    rankStageClopenCoreExtension e n a ha hclosed k v ∈
      rankStageGlobalBoundaryKernel e n J k :=
  InvariantClopenSectionExtension.extension_boundary_zero _ _ _ _ _
    (rankStageBoundaryIdeal (p := p) n k J) v hv

/-- Complementary cores have the same exact preimage equation as the cores. -/
theorem rankStageCoreComplement_preimage {k l : ℕ} (h : k ≤ l) :
    rankStageTransition (Over.mk p) n h ⁻¹ᵁ V l = V k := by
  ext x
  apply not_congr
  exact Iff.of_eq (congrArg (fun W ↦ x ∈ W) (rankStageCore_preimage e n a ha h))

/-- Uniqueness of extension by zero enforces every full order-transition equation. -/
theorem rankStageClopenCoreExtension_transition {k l : ℕ} (h : k ≤ l)
    (v : rankStageCoreInvariants e n a ha l) :
    rankStageInvariantTransition e n h (rankStageClopenCoreExtension e n a ha hclosed l v) =
      rankStageClopenCoreExtension e n a ha hclosed k (rankStageCoreRestriction e n a ha h v) := by
  apply Subtype.ext
  rw [rankStageInvariantTransition_val]
  unfold rankStageClopenCoreExtension InvariantClopenSectionExtension.extension
  simp only [rankStageCoreRestriction_val]
  exact pullback_extend_of_squares (U l) (V l) (inf_complement _ _) (sup_complement _ _)
    (U k) (V k) (inf_complement _ _) (sup_complement _ _)
    (rankStageTransition (Over.mk p) n h) (rankStageCoreMap e n a ha h)
    ((rankStageTransition (Over.mk p) n h).resLE (V l) (V k)
      (rankStageCoreComplement_preimage e n a ha hclosed h).ge)
    (rankStageCoreMap_inclusion e n a ha h) (Scheme.Hom.resLE_comp_ι _ _) v.val

end FLT.Mazur.EquivalenceRelationOrderedFrames

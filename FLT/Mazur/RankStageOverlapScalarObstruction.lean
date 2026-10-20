/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFiniteOriginalObstruction
public import FLT.Mazur.RankStageCoherentOverlapNumerators

/-!
# An exact finite original-scalar obstruction for all compatible overlap errors

The error towers are the actual differences of the independently chosen
core towers. One original-scalar quotient records simultaneous compatible
homogeneous extension of every pairwise error. Extending these errors is
not yet splitting the overlap cocycle by local corrections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance overlapScalarOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance overlapScalarOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance overlapScalarOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a b : Γ(A, ⊤))
  (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)
attribute [local irreducible] rankStageCore rankStageInvariantOverlapError

/-- The literal pairwise error is an element of the all-order compatible core ring. -/
def rankStageCompatibleOverlapError
    (u : rankStageCompatibleCoreInvariants e n a ha)
    (v : rankStageCompatibleCoreInvariants e n b hb) :
    rankStageCompatibleCoreInvariants e n (a * b) (rankStageProduct_domain n a b ha) :=
  ⟨fun k ↦ rankStageInvariantOverlapError e n a b ha hb k (u.val k) (v.val k),
    fun k l h ↦ by
      rw [rankStageInvariantOverlapError_transition, u.property k l h, v.property k l h]⟩

/-- Equal original boundary values put the entire error tower in the full boundary kernel. -/
theorem rankStageCompatibleOverlapError_boundary_zero
    (u : rankStageCompatibleCoreInvariants e n a ha)
    (v : rankStageCompatibleCoreInvariants e n b hb) (J : A.IdealSheafData)
    (t : Γ(J.subscheme, ⊤))
    (hu : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (u.val k).val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t)
    (hv : ∀ k, (rankStageCoreBoundaryIdeal e n b hb J k).subschemeι.appTop (v.val k).val =
      (rankStageCoreOriginalBoundaryMap e n b hb J k).appTop t) (k : ℕ) :
    (rankStageCoreBoundaryIdeal e n (a * b)
      (rankStageProduct_domain n a b ha) J k).subschemeι.appTop
        ((rankStageCompatibleOverlapError e n a b ha hb u v).val k).val = 0 :=
  rankStageInvariantOverlapError_boundary_zero e n a b ha hb J k
    (u.val k) (v.val k) t (hu k) (hv k)

variable {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j))

/-- One scalar ideal for all actual pairwise errors, including their infinite order towers. -/
def rankStageOverlapNumeratorIdeal : Ideal (compatibleFunctions p q) :=
  rankStageFamilyNumeratorIdeal e (fun _ : ι × ι ↦ n)
    (fun j ↦ c j.1 * c j.2) (fun j ↦ rankStageProduct_domain n (c j.1) (c j.2) (hc j.1)) J
    (fun j ↦ rankStageCompatibleOverlapError e n (c j.1) (c j.2) (hc j.1) (hc j.2)
      (v j.1) (v j.2))

/-- The entire selected error vector gives one finite cyclic module over original scalars. -/
theorem rankStageOverlapNumeratorQuotient_finite :
    Module.Finite (compatibleFunctions p q)
      ((compatibleFunctions p q) ⧸ rankStageOverlapNumeratorIdeal e n c hc J v) := inferInstance

/-- Killing its distinguished class is exactly simultaneous unscaled homogeneous extension. -/
theorem one_mem_rankStageOverlapNumeratorIdeal :
    1 ∈ rankStageOverlapNumeratorIdeal e n c hc J v ↔
      ∃ w : ∀ _ : ι × ι, ∀ k, rankStageInvariants e n k,
        (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
        (∀ j k l (h : k ≤ l), rankStageInvariantTransition e n h (w j l) = w j k) ∧
        ∀ j k, rankStageGlobalCoreRestriction e n (c j.1 * c j.2)
            (rankStageProduct_domain n (c j.1) (c j.2) (hc j.1)) k (w j k) =
          rankStageInvariantOverlapError e n (c j.1) (c j.2) (hc j.1) (hc j.2) k
            ((v j.1).val k) ((v j.2).val k) := by
  change 1 ∈ rankStageFamilyNumeratorIdeal _ _ _ _ _ _ ↔ _
  rw [mem_rankStageFamilyNumeratorIdeal]
  simp only [map_one, one_mul, rankStageCompatibleOverlapError]

end FLT.Mazur.EquivalenceRelationOrderedFrames

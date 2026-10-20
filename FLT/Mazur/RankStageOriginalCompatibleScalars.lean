/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCompatibleKernelObstruction

/-!
# Original invariant scalars acting on the all-order numerator obstruction

Original full-source invariants restrict to every rank order compatibly.
Pulling back the exact numerator ideal gives a cyclic finite obstruction
module over the unchanged original invariant ring. It is not the full
original boundary operator cokernel, and no vanishing is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance originalScalarOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance originalScalarOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance originalScalarOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ)

/-- Restriction of unchanged original full-source invariants to a whole rank stage. -/
def rankStageOriginalInvariantRestriction (k : ℕ) :
    compatibleFunctions p q →+* rankStageInvariants e n k :=
  relationPullback p q _ _ (rankThickeningMap (Over.mk p) n k)
    (rankStageArrow (p := p) n k) (rankStageFirst_isPullback (p := p) n k).w
    (rankStageSecond_map e n k).symm

omit [IsAffine A] [LocallyQuasiFinite p] in
/-- Full original scalar restrictions commute with every closed order transition. -/
theorem rankStageOriginalInvariantRestriction_transition {k l : ℕ} (h : k ≤ l)
    (s : compatibleFunctions p q) :
    rankStageInvariantTransition e n h (rankStageOriginalInvariantRestriction e n l s) =
      rankStageOriginalInvariantRestriction e n k s := by
  apply Subtype.ext
  change ((rankStageTransition (Over.mk p) n h) ≫
    rankThickeningMap (Over.mk p) n l).appTop s.val = _
  rw [rankStageTransition_map]
  rfl

/-- One original scalar acts simultaneously on every order of the actual global stage. -/
def rankStageOriginalCompatibleScalars :
    compatibleFunctions p q →+* rankStageCompatibleInvariants e n where
  toFun s := ⟨fun k ↦ rankStageOriginalInvariantRestriction e n k s,
    fun _ _ h ↦ rankStageOriginalInvariantRestriction_transition e n h s⟩
  map_zero' := Subtype.ext (funext fun k ↦ map_zero (rankStageOriginalInvariantRestriction e n k))
  map_one' := Subtype.ext (funext fun k ↦ map_one (rankStageOriginalInvariantRestriction e n k))
  map_add' s t := Subtype.ext
    (funext fun k ↦ map_add (rankStageOriginalInvariantRestriction e n k) s t)
  map_mul' s t := Subtype.ext
    (funext fun k ↦ map_mul (rankStageOriginalInvariantRestriction e n k) s t)

variable (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n a ha)

/-- Original scalars whose error multiple has full compatible homogeneous global lifts. -/
def rankStageOriginalNumeratorIdeal : Ideal (compatibleFunctions p q) :=
  Ideal.comap (rankStageOriginalCompatibleScalars e n)
    (rankStageCompatibleNumeratorIdeal e n a ha J x)

/-- The original-scalar obstruction retains exact all-order lifting, not stagewise lifting. -/
theorem mem_rankStageOriginalNumeratorIdeal (s : compatibleFunctions p q) :
    s ∈ rankStageOriginalNumeratorIdeal e n a ha J x ↔
      ∃ w : ∀ k, rankStageInvariants e n k,
        (∀ k, w k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
        (∀ k l (h : k ≤ l), rankStageInvariantTransition e n h (w l) = w k) ∧
        ∀ k, rankStageGlobalCoreRestriction e n a ha k (w k) =
          rankStageGlobalCoreRestriction e n a ha k
            (rankStageOriginalInvariantRestriction e n k s) * x.val k :=
  mem_rankStageCompatibleNumeratorIdeal e n a ha J x _

/-- The obstruction is finite over original invariant scalars, without a Noetherian assumption. -/
theorem rankStageOriginalNumeratorQuotient_finite :
    Module.Finite (compatibleFunctions p q)
      ((compatibleFunctions p q) ⧸ rankStageOriginalNumeratorIdeal e n a ha J x) := inferInstance

end FLT.Mazur.EquivalenceRelationOrderedFrames

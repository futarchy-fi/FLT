/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleNumeratorObstruction
public import FLT.Mazur.RankStageGlobalKernelLocalization

/-!
# The exact all-order homogeneous obstruction on actual rank stages

The source ring is formed from full global stage invariants, and its ideal
vanishes on the entire original boundary at every order. The norm is an
actual compatible element. Radical membership is equivalent to a genuinely
uniform exponent with ordinary compatible homogeneous global numerators.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance compatibleKernelOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance compatibleKernelOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance compatibleKernelOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
attribute [local irreducible] rankStageCore rankStageNormParameter
  rankStageInvariantTransition rankStageGlobalCoreRestriction rankStageCoreRestriction

/-- Compatible full global invariants at all comparable orders. -/
abbrev rankStageCompatibleInvariants :=
  CompatibleRingTower.ring (fun _ _ h ↦ rankStageInvariantTransition e n h)

/-- Compatible full invariants on the named affine core. -/
abbrev rankStageCompatibleCoreInvariants :=
  CompatibleRingTower.ring (fun _ _ h ↦ rankStageCoreRestriction e n a ha h)

/-- The entire homogeneous boundary ideal in the compatible global ring. -/
def rankStageCompatibleBoundaryKernel (J : A.IdealSheafData) :
    Ideal (rankStageCompatibleInvariants e n) :=
  CompatibleRingTower.ideal (fun _ _ h ↦ rankStageInvariantTransition e n h)
    (rankStageGlobalBoundaryKernel e n J)

/-- The global-to-core map retains exact compatibility at every order. -/
def rankStageCompatibleCoreRestriction :
    rankStageCompatibleInvariants e n →+* rankStageCompatibleCoreInvariants e n a ha :=
  CompatibleRingTower.map _ _ (rankStageGlobalCoreRestriction e n a ha)
    (fun _ _ h z ↦ rankStageGlobalCoreRestriction_transition e n a ha h z)

/-- Evaluation is the original full stage-to-core coefficient map. -/
theorem rankStageCompatibleCoreRestriction_val (w : rankStageCompatibleInvariants e n) (k : ℕ) :
    (rankStageCompatibleCoreRestriction e n a ha w).val k =
      rankStageGlobalCoreRestriction e n a ha k (w.val k) := rfl

variable (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n a ha)

/-- The actual scalar obstruction to compatible full homogeneous extension of a core tower. -/
def rankStageCompatibleNumeratorIdeal : Ideal (rankStageCompatibleInvariants e n) :=
  CompatibleRingTower.numeratorIdeal _ _ (rankStageGlobalCoreRestriction e n a ha)
    (fun _ _ h z ↦ rankStageGlobalCoreRestriction_transition e n a ha h z)
    (rankStageGlobalBoundaryKernel e n J) x

/-- Scalar membership has an actual all-order global homogeneous witness. -/
theorem mem_rankStageCompatibleNumeratorIdeal (b : rankStageCompatibleInvariants e n) :
    b ∈ rankStageCompatibleNumeratorIdeal e n a ha J x ↔
      ∃ w : ∀ k, rankStageInvariants e n k,
        (∀ k, w k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
        (∀ k l (h : k ≤ l), rankStageInvariantTransition e n h (w l) = w k) ∧
        ∀ k, rankStageGlobalCoreRestriction e n a ha k (w k) =
          rankStageGlobalCoreRestriction e n a ha k (b.val k) * x.val k :=
  CompatibleRingTower.mem_numeratorIdeal _ _ _ _ _ _ b

/-- The exact scalar obstruction module is finite over the compatible global ring. -/
theorem rankStageCompatibleNumeratorQuotient_finite :
    Module.Finite (rankStageCompatibleInvariants e n)
      ((rankStageCompatibleInvariants e n) ⧸ rankStageCompatibleNumeratorIdeal e n a ha J x) :=
  inferInstance

variable (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hC : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (hC c) k) = ⊤)

/-- The constructed norm parameters form one actual element of the compatible source ring. -/
def rankStageCompatibleNorm : rankStageCompatibleInvariants e n :=
  ⟨fun k ↦ rankStageNormParameter e n C hC hc a k, fun k l h ↦ by
    apply Subtype.ext
    rw [rankStageInvariantTransition_val]
    exact rankStageNormParameter_transition e n C hC hc a h⟩

/-- Norm radical membership is exactly a uniform compatible full-boundary numerator. -/
theorem rankStageCompatibleNorm_mem_radical_iff :
    rankStageCompatibleNorm e n a C hC hc ∈
        (rankStageCompatibleNumeratorIdeal e n a ha J x).radical ↔
      ∃ (N : ℕ) (w : ∀ k, rankStageInvariants e n k),
        (∀ k, w k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
        (∀ k l (h : k ≤ l), rankStageInvariantTransition e n h (w l) = w k) ∧
        ∀ k, rankStageGlobalCoreRestriction e n a ha k (w k) =
          (rankStageGlobalCoreRestriction e n a ha k
            (rankStageNormParameter e n C hC hc a k)) ^ N * x.val k :=
  CompatibleRingTower.mem_radical_numeratorIdeal _ _ _ _ _ _ _

end FLT.Mazur.EquivalenceRelationOrderedFrames

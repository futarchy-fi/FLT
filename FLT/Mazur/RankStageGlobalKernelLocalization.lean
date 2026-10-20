/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageGlobalBoundaryNumerators
public import FLT.Mazur.InvariantOpenGlobalRestriction
public import FLT.Mazur.SchemePrincipalSectionPowerDetection

/-!
# Full-stage boundary kernels and their principal-core restrictions

The actual global invariant ring maps to each full affine core. Its kernel
of restriction to the entire original boundary is an ideal. Global norm
powers detect equality on the core, and every local homogeneous error has
a numerator in that ideal. All coefficient squares retain order transitions.
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
local instance kernelLocOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance kernelLocOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance kernelLocOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
local notation "U" k => rankStageCore e n a ha k
attribute [local irreducible] rankStageCore rankStageNormParameter

/-- Full invariant restriction to the named affine core. -/
def rankStageGlobalCoreRestriction (k : ℕ) :
    rankStageInvariants e n k →+* rankStageCoreInvariants e n a ha k :=
  InvariantOpenCoefficientRestriction.globalRestriction _ _ (U k)
    (rankStageCore_invariant e n a ha k)

/-- The invariant map retains the literal full section restriction. -/
theorem rankStageGlobalCoreRestriction_val (k : ℕ) (w : rankStageInvariants e n k) :
    (rankStageGlobalCoreRestriction e n a ha k w).val = (U k).ι.appTop w.val := rfl

/-- Restricting globally or on the core gives the same full lower-order invariant. -/
theorem rankStageGlobalCoreRestriction_transition {k l : ℕ} (h : k ≤ l)
    (w : rankStageInvariants e n l) :
    rankStageGlobalCoreRestriction e n a ha k (rankStageInvariantTransition e n h w) =
      rankStageCoreRestriction e n a ha h (rankStageGlobalCoreRestriction e n a ha l w) := by
  apply Subtype.ext
  change ((U k).ι ≫ rankStageTransition (Over.mk p) n h).appTop w.val =
    (rankStageCoreMap e n a ha h ≫ (U l).ι).appTop w.val
  rw [rankStageCoreMap_inclusion]

variable (J : A.IdealSheafData)

/-- The kernel of restriction to the entire stage boundary in the global invariant ring. -/
def rankStageGlobalBoundaryKernel (k : ℕ) : Ideal (rankStageInvariants e n k) :=
  RingHom.ker ((rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop.hom.comp
    (compatibleFunctions (rankStageFirst (p := p) n k) (rankStageSecond e n k)).subtype)

omit [IsAffine A] [LocallyQuasiFinite p] in
/-- Membership is the exact full original boundary equation. -/
theorem mem_rankStageGlobalBoundaryKernel (k : ℕ) (w : rankStageInvariants e n k) :
    w ∈ rankStageGlobalBoundaryKernel e n J k ↔
      (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop w.val = 0 := Iff.rfl

omit [IsAffine A] [LocallyQuasiFinite p] in
/-- Every closed order transition preserves the full homogeneous boundary ideal. -/
theorem rankStageGlobalBoundaryKernel_transition {k l : ℕ} (h : k ≤ l)
    (w : rankStageInvariants e n l) (hw : w ∈ rankStageGlobalBoundaryKernel e n J l) :
    rankStageInvariantTransition e n h w ∈ rankStageGlobalBoundaryKernel e n J k := by
  rw [mem_rankStageGlobalBoundaryKernel] at hw ⊢
  change (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop
    ((rankStageTransition (Over.mk p) n h).appTop w.val) = 0
  rw [IdealSheafClosedTransitions.section_square _ _ _
    (rankStageBoundaryIdeal_transition n h J), hw, map_zero]

variable (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hC : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (hC c) k) = ⊤)
local notation "r" k => rankStageNormParameter e n C hC hc a k

/-- Equality on a core is detected by one power in the full global invariant ring. -/
theorem rankStageGlobalCoreRestriction_power_eq (k : ℕ) (v w : rankStageInvariants e n k)
    (h : rankStageGlobalCoreRestriction e n a ha k v =
      rankStageGlobalCoreRestriction e n a ha k w) :
    ∃ N : ℕ, (r k) ^ N * v = (r k) ^ N * w := by
  let _ := rankStage_compact_of_core_cover e n C hC hc k
  let _ : QuasiSeparated (rankThickeningMap (Over.mk p) n k) := by
    unfold rankThickeningMap
    infer_instance
  let _ := quasiSeparatedSpace_of_quasiSeparated (rankThickeningMap (Over.mk p) n k)
  obtain ⟨N, hN⟩ := SchemePrincipalSectionPowerDetection.exists_power_eq (r k).val (U k)
    (rankStageNormParameter_basicOpen e n C hC hc a ha k) v.val w.val
    (congrArg Subtype.val h)
  exact ⟨N, Subtype.ext hN⟩

/-- Every homogeneous core value has a numerator in the actual global boundary ideal. -/
theorem exists_rankStageGlobalBoundaryKernel_numerator (k : ℕ)
    (v : rankStageCoreInvariants e n a ha k)
    (hv : (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop v.val = 0) :
    ∃ (N : ℕ) (w : rankStageInvariants e n k),
      w ∈ rankStageGlobalBoundaryKernel e n J k ∧
      rankStageGlobalCoreRestriction e n a ha k w =
        (rankStageGlobalCoreRestriction e n a ha k (r k)) ^ N * v := by
  obtain ⟨N, w, hw, he⟩ := exists_rankStage_global_kernel_numerator e n C hC hc a ha J k v hv
  exact ⟨N, w, hw, Subtype.ext he⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames

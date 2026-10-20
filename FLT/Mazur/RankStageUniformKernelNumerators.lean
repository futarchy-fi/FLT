/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageRescaledGlobalKernelTowers

/-!
# Ordinary compatible homogeneous numerators on every finite order interval

Normalize the constructed rescaled tower to its exponent at the last order.
This gives one exact exponent and ordinary compatibility throughout the chosen
finite interval. The interval bound is explicit; it is not a uniform bound
for the infinite tower. The numerators still represent scaled core errors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem normalize_transition {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (s : S) (hr : f r = s) (w : R) (z : S)
    (L K B : ℕ) (hK : K ≤ L) (hB : L ≤ B) (hw : f w = s ^ (L - K) * z) :
    f (r ^ (B - L) * w) = s ^ (B - K) * z := by
  rw [map_mul, map_pow, hr, hw, ← mul_assoc, ← pow_add]
  congr 2
  omega

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance uniformNumOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance uniformNumOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance uniformNumOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hC : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (hC c) k) = ⊤)
  (J : A.IdealSheafData) {ι : Type*} [Finite ι]
  (a : ι → Γ(A, ⊤)) (ha : ∀ j, A.basicOpen (a j) ≤ rankImageOpen (Over.mk p) n)
local notation "r" j:max k:max => rankStageNormParameter e n C hC hc (a j) k
local notation "F" j:max k:max => rankStageGlobalCoreRestriction e n (a j) (ha j) k
attribute [local irreducible] rankStageCore rankStageNormParameter
  rankStageInvariantTransition rankStageGlobalCoreRestriction

/-- Every finite truncation has one exponent and ordinary full-stage compatible numerators. -/
theorem exists_rankStage_finite_interval_kernel_numerators
    (v : ∀ j k, rankStageCoreInvariants e n (a j) (ha j) k)
    (hv : ∀ j k, (rankStageCoreBoundaryIdeal e n (a j) (ha j) J k).subschemeι.appTop
      (v j k).val = 0)
    (ht : ∀ j k l (h : k ≤ l), rankStageCoreRestriction e n (a j) (ha j) h (v j l) = v j k)
    (H : ℕ) :
    ∃ (B : ℕ) (z : ∀ k, ι → rankStageInvariants e n k),
      (∀ k j, z k j ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ k, k ≤ H → ∀ j, (F j k) (z k j) = ((F j k) (r j k)) ^ B * v j k) ∧
      ∀ k l (h : k ≤ l), l ≤ H → ∀ j, rankStageInvariantTransition e n h (z l j) = z k j := by
  obtain ⟨N, w, hN, hw, he, hh⟩ :=
    exists_rankStage_rescaled_global_kernel_towers e n C hC hc J a ha v hv ht
  refine ⟨N H, fun k j ↦ (r j k) ^ (N H - N k) * w k j,
    fun k j ↦ (rankStageGlobalBoundaryKernel e n J k).mul_mem_left _ (hw k j), ?_, ?_⟩
  · intro k hk j
    exact PrincipalNumeratorTransition.promote (F j k) (r j k) (w k j) (v j k)
      (hN hk) (he k j)
  · intro k l h hl j
    have hr : rankStageInvariantTransition e n h (r j l) = r j k :=
      by
        apply Subtype.ext
        rw [rankStageInvariantTransition_val]
        exact rankStageNormParameter_transition e n C hC hc (a j) h
    exact normalize_transition (rankStageInvariantTransition e n h) (r j l) (r j k) hr
      (w l j) (w k j) (N l) (N k) (N H) (hN h) (hN hl) (hh k l h j)

end FLT.Mazur.EquivalenceRelationOrderedFrames

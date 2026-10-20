/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreOriginalEnvelope
public import FLT.Mazur.RankStageCoreCoefficientTransitions

/-!
# Original affine representatives of actual rank-core coefficients

Fix an original principal neighborhood whose inverse image lies in every core.
Every full core coefficient then has a representative on the same original
affine neighborhood. The kernel is the actual power of the rank ideal there.
These are powers on the original source, not on its invariant scalar ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance affineRepOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance affineRepOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance affineRepOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "C" => rankStageCore e n a ha

/-- The fixed affine neighborhood is an open of the unchanged original rank-image open. -/
def rankStageOriginalAffineOpen : (X).affineOpens :=
  ⟨(rankImageOpen (Over.mk p) n).ι ⁻¹ᵁ A.basicOpen b,
    ((isAffineOpen_top A).basicOpen b).preimage_of_isOpenImmersion _ (by
      simpa only [Scheme.Opens.opensRange_ι] using hb)⟩

local notation "U" => rankStageOriginalAffineOpen (p := p) n b hb

/-- Restrict an actual core coefficient to the fixed original principal neighborhood. -/
def rankStageCoreAffineCoefficient (k : ℕ)
    (h : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C k)
    (v : Γ((C k).toScheme, ⊤)) :
    Γ((I ^ (k + 1)).subscheme, (I ^ (k + 1)).subschemeι ⁻¹ᵁ U.1) :=
  (rankThickening (Over.mk p) n k).presheaf.map (homOfLE h).op ((C k).topIso.hom v)

/-- Every full coefficient lifts to an actual section on this fixed original affine open. -/
theorem exists_rankStage_original_affine_representative (k : ℕ)
    (h : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C k)
    (v : Γ((C k).toScheme, ⊤)) :
    ∃ w : Γ(X, U.1), (I ^ (k + 1)).subschemeι.app U.1 w =
      rankStageCoreAffineCoefficient e n a ha b hb k h v :=
  (I ^ (k + 1)).subschemeι_app_surjective U _

omit [QuasiCompact p] [IsLocallyNoetherian A] [LocallyQuasiFinite p] in
/-- Two original representatives differ by the full rank ideal power, including nilpotents. -/
theorem rankStage_original_affine_same_image_iff (k : ℕ) (w z : Γ(X, U.1)) :
    (I ^ (k + 1)).subschemeι.app U.1 w = (I ^ (k + 1)).subschemeι.app U.1 z ↔
      w - z ∈ ((I).ideal U) ^ (k + 1) := by
  change _ ↔ w - z ∈ (I ^ (k + 1)).ideal U
  rw [← (I ^ (k + 1)).ker_subschemeι_app U]
  change _ ↔ (I ^ (k + 1)).subschemeι.app U.1 (w - z) = 0
  rw [map_sub, sub_eq_zero]

/-- A full sequence of core coefficients has representatives on one original affine ring. -/
theorem exists_rankStage_original_affine_representatives
    (h : ∀ k : ℕ, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C k)
    (v : ∀ k : ℕ, Γ((C k).toScheme, ⊤)) :
    ∃ w : ℕ → Γ(X, U.1), ∀ k : ℕ, (I ^ (k + 1)).subschemeι.app U.1 (w k) =
      rankStageCoreAffineCoefficient e n a ha b hb k (h k) (v k) := by
  exact Classical.axiomOfChoice fun k ↦
    exists_rankStage_original_affine_representative e n a ha b hb k (h k) (v k)

end FLT.Mazur.EquivalenceRelationOrderedFrames

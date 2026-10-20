/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundedCoreCover
public import FLT.Mazur.RankStageCorePointTests

/-!
# Finite families of coherent cores detect full original coefficients

The constructed finite original cover gives jointly injective section tests
on every locally Noetherian coefficient scheme over that domain. All orders
are retained, so nilpotents and lower-rank points are detected. This is an
injectivity theorem, not a construction of compatible lifts between cores.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeInfinitesimalPointDetection
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance coreDetectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coreDetectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coreDetectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCore rankStageCoreOriginalMap
variable [IsLocallyNoetherian B] (g : B ⟶ A)

/-- Covered core orders detect sections on the full unchanged coefficient scheme. -/
theorem section_zero_of_selected_core_orders {ι : Type}
    (n : ι → ℕ) (a b : ι → Γ(A, ⊤))
    (ha : ∀ i, A.basicOpen (a i) ≤ rankImageOpen (Over.mk p) (n i))
    (h : ∀ i k, rankThickeningMap (Over.mk p) (n i) k ⁻¹ᵁ A.basicOpen (b i) ≤
      rankStageCore e (n i) (a i) (ha i) k)
    (hcover : ∀ x : B, ∃ i, g x ∈ exactRank (Over.mk p) (n i) ∧
      g x ∈ A.basicOpen (b i))
    (s : Γ(B, ⊤))
    (hs : ∀ i order,
      (pullback.snd (rankStageCoreOriginalMap e (n i) (a i) (ha i) order) g).appTop s = 0) :
    s = 0 := by
  apply section_eq_zero B s
  intro x k
  obtain ⟨i, hi, hb⟩ := hcover x
  exact pointThickening_zero_of_core_orders e (n i) (a i) (ha i) (b i) (h i)
    g x hi hb s (hs i) k

/-- The same all-order tests compare two arbitrary original coefficients. -/
theorem section_eq_of_selected_core_orders {ι : Type}
    (n : ι → ℕ) (a b : ι → Γ(A, ⊤))
    (ha : ∀ i, A.basicOpen (a i) ≤ rankImageOpen (Over.mk p) (n i))
    (h : ∀ i k, rankThickeningMap (Over.mk p) (n i) k ⁻¹ᵁ A.basicOpen (b i) ≤
      rankStageCore e (n i) (a i) (ha i) k)
    (hcover : ∀ x : B, ∃ i, g x ∈ exactRank (Over.mk p) (n i) ∧
      g x ∈ A.basicOpen (b i))
    (s t : Γ(B, ⊤))
    (hst : ∀ i order,
      (pullback.snd (rankStageCoreOriginalMap e (n i) (a i) (ha i) order) g).appTop s =
        (pullback.snd (rankStageCoreOriginalMap e (n i) (a i) (ha i) order) g).appTop t) :
    s = t := by
  apply sub_eq_zero.mp
  apply section_zero_of_selected_core_orders e g n a b ha h hcover (s - t)
  intro i order
  rw [map_sub, hst, sub_self]

/-- Finite original core data with jointly injective tests are constructed without fiber bounds. -/
theorem exists_finite_original_core_detection (W : A.Opens) (hg : ∀ x : B, g x ∈ W) :
    ∃ (N : ℕ) (C : Fin (N + 1) → Finset (Γ(A, ⊤) × Γ(A, ⊤)))
      (ha : ∀ n (c : C n), A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n.val),
      (∀ n (c : C n), A.basicOpen c.val.2 ≤ W) ∧
      (∀ n (c : C n) order,
        rankThickeningMap (Over.mk p) n.val order ⁻¹ᵁ A.basicOpen c.val.2 ≤
          rankStageCore e n.val c.val.1 (ha n c) order) ∧
      ∀ s : Γ(B, ⊤),
        (∀ n (c : C n) order,
          (pullback.snd (rankStageCoreOriginalMap e n.val c.val.1 (ha n c) order) g).appTop s =
            0) → s = 0 := by
  classical
  obtain ⟨N, C, hC, hcover⟩ := exists_rankStage_bounded_original_core_cover e W
  have hex (n : Fin (N + 1)) (c : C n) := hC n c.val c.property
  choose ha hW hb hc using hex
  refine ⟨N, C, ha, hW, hc, fun s hs ↦ ?_⟩
  apply section_zero_of_selected_core_orders e g
    (fun i : Σ n, C n ↦ i.1.val) (fun i ↦ i.2.val.1) (fun i ↦ i.2.val.2)
    (fun i ↦ ha i.1 i.2) (fun i ↦ hc i.1 i.2) ?_ s (fun i ↦ hs i.1 i.2)
  intro x
  obtain ⟨n, hn, c, hmem, hxc⟩ := hcover (g x) (hg x)
  exact ⟨⟨n, ⟨c, hmem⟩⟩, hn, hxc⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames

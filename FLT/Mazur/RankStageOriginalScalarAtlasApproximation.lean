/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalAtlasTower
public import FLT.Mazur.SchemeRelationAtlasOperator
public import FLT.Mazur.BoundaryCorrectionAdicEquationSupport

/-!
# Constructed full atlas approximations over original invariant scalars

The original boundary constructs the entire coupled rank-error tower. The
literal section vector is now identified with the scalar-linear operator.
Full scalar support and finite generation of the equation ideal yield every
scalar approximation; no source-Cauchy argument substitutes for mixed equations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance scalarAtlasOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarAtlasOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarAtlasOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  {ι : Type} [Finite ι] (b : ι → Γ(A, ⊤))
  (hb : ∀ i, A.basicOpen (b i) ≤ rankImageOpen (Over.mk p) n)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "U" i => rankStageOriginalAffineOpen (p := p) n (b i) (hb i)
attribute [local irreducible] rankStageCore


variable
  (h : ∀ k i, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen (b i) ≤
      rankStageCore e n a ha k)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
    [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : SchemeEffectiveEpiSections.compatibleFunctions
    (CategoryTheory.Limits.pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
  (B : ι → Scheme.{0}) [∀ i, IsAffine (B i)]
  (gB : ∀ i, B i ⟶ (rankImageOpen (Over.mk p) n).toScheme)
  (hgB : ∀ i, ⊤ ≤ gB i ⁻¹ᵁ (rankStageOriginalAffineOpen (p := p) n (b i) (hb i)).1)
  (d : ∀ i, B i ⟶ J.subscheme)
  (hd : ∀ i, gB i ≫ (rankImageOpen (Over.mk p) n).ι = d i ≫ J.subschemeι)
  (M : ι → ι → Scheme.{0}) [∀ i j, IsAffine (M i j)]
  (gM gM' : ∀ i j, M i j ⟶ (rankImageOpen (Over.mk p) n).toScheme)
  (hgM : ∀ i j, ⊤ ≤ gM i j ⁻¹ᵁ (rankStageOriginalAffineOpen (p := p) n (b i) (hb i)).1)
  (hgM' : ∀ i j, ⊤ ≤ gM' i j ⁻¹ᵁ (rankStageOriginalAffineOpen (p := p) n (b j) (hb j)).1)
  (δ : ∀ i j, M i j ⟶ D)
  (hδ : ∀ i j, δ i j ≫ p = gM i j ≫ (rankImageOpen (Over.mk p) n).ι)
  (hδ' : ∀ i j, δ i j ≫ q = gM' i j ≫ (rankImageOpen (Over.mk p) n).ι)

local notation "Ω" => SchemeEffectiveEpiSections.compatibleFunctions p q
local notation "j" => (rankImageOpen (Over.mk p) n).ι
local notation "K" => BoundaryCorrectionIdeal.fullEquationIdeal
  (fun i ↦ ((I).comap (gB i)).ideal ⟨⊤, isAffineOpen_top (B i)⟩)
  (fun i l ↦ ((I).comap (gM i l)).ideal ⟨⊤, isAffineOpen_top (M i l)⟩)
local notation "F" => SchemeRelationAtlasOperator.operator p q j (fun i ↦ (U i).1)
  B gB hgB M gM gM' hgM hgM' δ hδ hδ'
local notation "v" => ((fun i ↦ (d i).appTop t.val), (0 : ∀ i l, Γ(M i l, ⊤)))

include h hf hd

/-- The actual boundary constructs every rank approximation of the scalar-linear operator. -/
theorem exists_rankStage_original_operator_errors :
    ∀ k : ℕ, ∃ w : ∀ i, Γ(X, (U i).1), v - F w ∈ K ^ (k + 1) := by
  obtain ⟨w, hw, _⟩ := exists_rankStage_original_atlas_tower e n a ha b hb h J hJ f hf t
    B gB hgB d hd M gM gM' hgM hgM' δ hδ hδ'
  intro k
  refine ⟨w k, ?_⟩
  simpa only [SchemeRelationAtlasOperator.operator_apply] using hw k

/-- Whole equation-ring support converts the constructed coupled tower to scalar errors. -/
theorem exists_rankStage_original_scalar_atlas_approximations :
    let _ : ∀ i, Algebra Ω Γ(X, (U i).1) :=
      fun i ↦ SchemeRelationSectionScalars.sectionAlgebra p q j (U i).1
    let _ : ∀ i, Algebra Ω Γ(B i, ⊤) :=
      fun i ↦ SchemeRelationSectionScalars.sectionAlgebra p q (gB i ≫ j) ⊤
    let _ : ∀ i l, Algebra Ω Γ(M i l, ⊤) :=
      fun i l ↦ SchemeRelationSectionScalars.sectionAlgebra p q (gM i l ≫ j) ⊤
    ∀ Q : Ideal Ω, (K).FG →
    PrimeSpectrum.zeroLocus
      (Q.map (algebraMap Ω ((∀ i, Γ(B i, ⊤)) × ∀ i l, Γ(M i l, ⊤))) :
        Set ((∀ i, Γ(B i, ⊤)) × ∀ i l, Γ(M i l, ⊤))) ⊆
      PrimeSpectrum.zeroLocus (K : Set ((∀ i, Γ(B i, ⊤)) × ∀ i l, Γ(M i l, ⊤))) →
    ∀ k : ℕ, ∃ w : ∀ i, Γ(X, (U i).1), v - F w ∈
      Q ^ (k + 1) • (⊤ : Submodule Ω ((∀ i, Γ(B i, ⊤)) × ∀ i l, Γ(M i l, ⊤))) := by
  let _ : ∀ i, Algebra Ω Γ(X, (U i).1) :=
    fun i ↦ SchemeRelationSectionScalars.sectionAlgebra p q j (U i).1
  let _ : ∀ i, Algebra Ω Γ(B i, ⊤) :=
    fun i ↦ SchemeRelationSectionScalars.sectionAlgebra p q (gB i ≫ j) ⊤
  let _ : ∀ i l, Algebra Ω Γ(M i l, ⊤) :=
    fun i l ↦ SchemeRelationSectionScalars.sectionAlgebra p q (gM i l ≫ j) ⊤
  dsimp only
  intro Q hfg hsupport
  apply AdicIdealPowerComparison.scalar_approximations Q K F v hfg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hsupport)
  exact exists_rankStage_original_operator_errors e n a ha b hb h J hJ f hf t
    B gB hgB d hd M gM gM' hgM hgM' δ hδ hδ'

end FLT.Mazur.EquivalenceRelationOrderedFrames

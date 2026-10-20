/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalScalarAtlasApproximation
public import FLT.Mazur.RankStageOriginalScalarSupport
public import FLT.Mazur.SchemeRelationAtlasOperator
public import FLT.Mazur.BoundaryCorrectionAdicEquationSupport

/-!
# Scalar approximations from full geometric rank tests on the original atlas

Noetherian coordinate schemes prove finite generation of the coupled equation
ideal. Full geometric scalar-locus rank tests prove its support condition.
The prescribed original boundary then constructs every scalar approximation
of the original operator, retaining all boundary and mixed coordinates.
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
local instance geometricAtlasOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance geometricAtlasOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance geometricAtlasOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
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

variable [∀ i, IsLocallyNoetherian (B i)] [∀ i l, IsLocallyNoetherian (M i l)]

include h hf hd in
/-- Geometric rank tests and original coordinate finiteness suffice for the coupled errors. -/
theorem exists_rankStage_original_geometric_atlas_approximations :
    let _ : ∀ i, Algebra Ω Γ(X, (U i).1) :=
      fun i ↦ SchemeRelationSectionScalars.sectionAlgebra p q j (U i).1
    let _ : ∀ i, Algebra Ω Γ(B i, ⊤) :=
      fun i ↦ SchemeRelationSectionScalars.sectionAlgebra p q (gB i ≫ j) ⊤
    let _ : ∀ i l, Algebra Ω Γ(M i l, ⊤) :=
      fun i l ↦ SchemeRelationSectionScalars.sectionAlgebra p q (gM i l ≫ j) ⊤
    ∀ Q : Ideal Ω,
      (∀ i x, SchemeScalarPrincipalNeighborhood.scalarMorphism
        (SchemeRelationSectionScalars.scalarMap p q (gB i ≫ j) ⊤) x ∈
          PrimeSpectrum.zeroLocus (Q : Set Ω) →
        (gB i ≫ j) x ∈ exactRank (Over.mk p) n) →
      (∀ i l x, SchemeScalarPrincipalNeighborhood.scalarMorphism
        (SchemeRelationSectionScalars.scalarMap p q (gM i l ≫ j) ⊤) x ∈
          PrimeSpectrum.zeroLocus (Q : Set Ω) →
        (gM i l ≫ j) x ∈ exactRank (Over.mk p) n) →
      ∀ k : ℕ, ∃ w : ∀ i, Γ(X, (U i).1), v - F w ∈
        Q ^ (k + 1) • (⊤ : Submodule Ω ((∀ i, Γ(B i, ⊤)) × ∀ i l, Γ(M i l, ⊤))) := by
  let _ : ∀ i, Algebra Ω Γ(X, (U i).1) :=
    fun i ↦ SchemeRelationSectionScalars.sectionAlgebra p q j (U i).1
  let _ : ∀ i, Algebra Ω Γ(B i, ⊤) :=
    fun i ↦ SchemeRelationSectionScalars.sectionAlgebra p q (gB i ≫ j) ⊤
  let _ : ∀ i l, Algebra Ω Γ(M i l, ⊤) :=
    fun i l ↦ SchemeRelationSectionScalars.sectionAlgebra p q (gM i l ≫ j) ⊤
  let _ : ∀ i, IsNoetherianRing Γ(B i, ⊤) :=
    fun i ↦ IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (B i)⟩
  let _ : ∀ i l, IsNoetherianRing Γ(M i l, ⊤) :=
    fun i l ↦ IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (M i l)⟩
  dsimp only
  intro Q hB hM
  apply exists_rankStage_original_scalar_atlas_approximations e n a ha b hb h J hJ f hf t
    B gB hgB d hd M gM gM' hgM hgM' δ hδ hδ' Q
  · exact BoundaryCorrectionIdeal.fullEquationIdeal_fg _ _
  · apply BoundaryCorrectionIdeal.fullEquationIdeal_scalar_support
    · intro i
      exact rankStage_original_scalar_support (Over.mk p) n
        (SchemeRelationSectionScalars.scalarMap p q (gB i ≫ j) ⊤) Q (gB i) (hB i)
    · intro i l
      exact rankStage_original_scalar_support (Over.mk p) n
        (SchemeRelationSectionScalars.scalarMap p q (gM i l ≫ j) ⊤) Q (gM i l) (hM i l)

end FLT.Mazur.EquivalenceRelationOrderedFrames

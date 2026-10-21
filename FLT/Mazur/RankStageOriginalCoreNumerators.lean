/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalPrincipalNumerators

/-!
# Original scalars defining arbitrary stage cores

Homogeneous denominator clearing only needs the stage core to be the
principal open of the restricted original scalar. The input chart parameter
itself need not be invariant or agree with that scalar.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem originalCore_kernel_numerator {T X : Scheme.{0}}
    (p q : T ⟶ X) [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace T] [QuasiSeparatedSpace T] (r : compatibleFunctions p q)
    (I : X.IdealSheafData) [CompactSpace I.subscheme] [QuasiSeparatedSpace I.subscheme]
    (U : X.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (hUr : U = X.basicOpen r.val)
    (v : InvariantOpenCoefficientRestriction.coefficients p q U hU)
    (hv : (I.comap U.ι).subschemeι.appTop v.val = 0) :
    ∃ (N : ℕ) (w : compatibleFunctions p q), I.subschemeι.appTop w.val = 0 ∧
      InvariantOpenCoefficientRestriction.globalRestriction p q U hU w =
        (InvariantOpenCoefficientRestriction.globalRestriction p q U hU r) ^ N * v := by
  obtain ⟨N, w, hb, he⟩ :=
    SchemeRelationQcqsBoundaryNumerator.exists_ideal_kernel_numerator p q r I U hU hUr v hv
  exact ⟨N, w, hb, Subtype.ext he⟩

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance coreOriginalOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coreOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coreOriginalOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤))
  (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n) (k : ℕ)
local notation "X" => rankThickening (Over.mk p) n k
local notation "U" => rankStageCore e n a ha k

omit [QuasiCompact p] [LocallyQuasiFinite p] in
private theorem originalCoreStage_compact : CompactSpace (X) := by
  let _ : IsNoetherian A := ⟨⟩
  let _ : NoetherianSpace (rankImageOpen (Over.mk p) n).toScheme :=
    NoetherianSpace.set (rankImageOpen (Over.mk p) n : Set A)
  let _ : IsNoetherian (rankImageOpen (Over.mk p) n).toScheme := ⟨⟩
  exact QuasiCompact.compactSpace_of_compactSpace
    (rankStratumIdeal (Over.mk p) n ^ (k + 1)).subschemeι

attribute [local irreducible] rankStageCore rankStageOriginalInvariantRestriction
  rankStageFirst rankStageSecond rankStageBoundaryIdeal
variable (J : A.IdealSheafData) (s : compatibleFunctions p q)
  (hs : rankStageCore e n a ha k =
    (rankThickening (Over.mk p) n k).basicOpen
      (rankStageOriginalInvariantRestriction e n k s).val)
local notation "r" => rankStageOriginalInvariantRestriction e n k s

include hs in
/-- An original scalar defining the actual core clears full homogeneous denominators. -/
theorem exists_rankStage_original_core_numerator
    (v : rankStageCoreInvariants e n a ha k)
    (hv : (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop v.val = 0) :
    ∃ (N : ℕ) (w : rankStageInvariants e n k),
      w ∈ rankStageGlobalBoundaryKernel e n J k ∧
      rankStageGlobalCoreRestriction e n a ha k w =
        (rankStageGlobalCoreRestriction e n a ha k r) ^ N * v := by
  let _ := originalCoreStage_compact (p := p) n k
  let _ : QuasiSeparated (rankThickeningMap (Over.mk p) n k) := by
    unfold rankThickeningMap
    infer_instance
  let _ := quasiSeparatedSpace_of_quasiSeparated (rankThickeningMap (Over.mk p) n k)
  let _ := rankStageFirst_finite (p := p) n k
  let _ := QuasiCompact.compactSpace_of_compactSpace (rankStageFirst (p := p) n k)
  let _ := quasiSeparatedSpace_of_quasiSeparated (rankStageFirst (p := p) n k)
  let I := rankStageBoundaryIdeal (p := p) n k J
  let _ := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let _ := quasiSeparatedSpace_of_quasiSeparated I.subschemeι
  exact originalCore_kernel_numerator _ _ r I U
    (rankStageCore_invariant e n a ha k) hs v hv

end FLT.Mazur.EquivalenceRelationOrderedFrames

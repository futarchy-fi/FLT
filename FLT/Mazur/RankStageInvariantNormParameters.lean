/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantAffineCoverNorm
public import FLT.Mazur.InvariantAffineOpenNormBaseChange
public import FLT.Mazur.RankStageFiniteCoreGluing

/-!
# Coherent global invariant parameters for the actual finite rank-core cover

The rank stage need not be affine. Its full affine cores construct global
norm scalars whose principal opens are precisely those cores. The scalars
are compatible at every infinitesimal order, without choosing denominators
or assuming an invariant partition of unity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections InvariantAffineCoverNorm
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance normOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance normOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance normOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (ha : ∀ c : C, A.basicOpen (c).val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n (c).val.1 (ha c) k) = ⊤)
local instance normFirst_finite (k : ℕ) : IsFinite (rankStageFirst (p := p) n k) :=
  rankStageFirst_finite n k
local notation "X" k => rankThickening (Over.mk p) n k
local notation "U" c:max k:max => rankStageCore e n (c).val.1 (ha c) k
local notation "hU" c:max k:max => rankStageCore_invariant e n (c).val.1 (ha c) k
local notation "aU" c:max k:max => rankStageCore_affine e n (c).val.1 (ha c) k
local notation "aUV" k => fun c d : C ↦
  rankStageCore_intersection_affine e n (c).val.1 (d).val.1 (ha c) (ha d) k
attribute [local irreducible] rankStageCore

/-- The original parameter gives a full global invariant norm at each rank order. -/
def rankStageNormParameter (a : Γ(A, ⊤)) (k : ℕ) :
    compatibleFunctions (rankStageFirst (p := p) n k) (rankStageSecond e n k) :=
  globalCoefficient _ _ (rankStageEquivalence e n k) (fun c : C ↦ U c k)
    (fun c ↦ hU c k) (fun c ↦ aU c k) (aUV k) (hc k)
    ((rankThickeningMap (Over.mk p) n k).appTop a)

/-- Its restriction is the norm of the complete relation over the named core. -/
theorem rankStageNormParameter_restrict (a : Γ(A, ⊤)) (k : ℕ) (c : C) :
    (U c k).ι.appTop (rankStageNormParameter e n C ha hc a k).val =
      (InvariantAffineOpenNormCoefficient.coefficient _ _ (rankStageEquivalence e n k)
        (U c k) (hU c k) (aU c k) ((rankThickeningMap (Over.mk p) n k).appTop a)).val :=
  globalCoefficient_restrict _ _ (rankStageEquivalence e n k) (fun c : C ↦ U c k)
    (fun c ↦ hU c k) (fun c ↦ aU c k) (aUV k) (hc k)
    ((rankThickeningMap (Over.mk p) n k).appTop a) c

/-- The global invariant scalar defines exactly the original whole-orbit affine core. -/
theorem rankStageNormParameter_basicOpen (a : Γ(A, ⊤))
    (ha' : A.basicOpen a ≤ rankImageOpen (Over.mk p) n) (k : ℕ) :
    (X k).basicOpen (rankStageNormParameter e n C ha hc a k).val =
      rankStageCore e n a ha' k := by
  conv_rhs => unfold rankStageCore
  exact basicOpen_globalCoefficient _ _ (rankStageEquivalence e n k) (fun c : C ↦ U c k)
    (fun c ↦ hU c k) (fun c ↦ aU c k) (aUV k) (hc k)
    ((rankThickeningMap (Over.mk p) n k).appTop a) (rankStagePrincipal_affine n a ha' k)

attribute [local irreducible] rankStageNormParameter

/-- The selected global invariant parameters give the actual finite cover at every order. -/
theorem rankStageNormParameter_cover (k : ℕ) :
    (⨆ c : C, (X k).basicOpen
      (rankStageNormParameter e n C ha hc (c).val.1 k).val) = ⊤ := by
  simp only [rankStageNormParameter_basicOpen e n C ha hc _ (ha _) k]
  exact hc k

/-- All closed order transitions preserve the constructed global norm parameters exactly. -/
theorem rankStageNormParameter_transition (a : Γ(A, ⊤)) {k l : ℕ} (hkl : k ≤ l) :
    (rankStageTransition (Over.mk p) n hkl).appTop
      (rankStageNormParameter e n C ha hc a l).val =
        (rankStageNormParameter e n C ha hc a k).val := by
  apply InvariantOpenCoefficientGluing.section_ext (fun c : C ↦ U c k) (hc k)
  intro c
  rw [rankStageNormParameter_restrict]
  change ((U c k).ι ≫ rankStageTransition (Over.mk p) n hkl).appTop _ = _
  rw [← rankStageCoreMap_inclusion]
  change (rankStageCoreMap e n (c).val.1 (ha c) hkl).appTop ((U c l).ι.appTop _) = _
  rw [rankStageNormParameter_restrict]
  have he := InvariantAffineOpenNormCoefficient.coefficient_baseChange _ _ _ _
    (rankStageEquivalence e n l) (rankStageEquivalence e n k)
    (rankStageTransition (Over.mk p) n hkl) (rankStageRelationTransition (p := p) n hkl)
    (rankStageRelationTransition_isPullback n hkl) (rankStageRelationTransition_second e n hkl)
    (U c l) (U c k) (hU c l) (hU c k) (aU c l) (aU c k)
    (rankStageCore_preimage e n (c).val.1 (ha c) hkl).symm
    ((rankThickeningMap (Over.mk p) n l).appTop a)
  have hs : (rankStageTransition (Over.mk p) n hkl).appTop
      ((rankThickeningMap (Over.mk p) n l).appTop a) =
        (rankThickeningMap (Over.mk p) n k).appTop a := by
    change (rankStageTransition (Over.mk p) n hkl ≫
      rankThickeningMap (Over.mk p) n l).appTop a = _
    rw [rankStageTransition_map]
  rw [hs] at he
  exact he.symm

end FLT.Mazur.EquivalenceRelationOrderedFrames

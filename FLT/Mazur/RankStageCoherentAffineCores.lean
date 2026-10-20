/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageRelationTransitions
public import FLT.Mazur.FiniteRelationAffineCoreBaseChange
public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood

/-!
# A coherent affine invariant domain at every rank order

One parameter on the original affine source gives affine principal domains at
all orders. Their whole-orbit norm cores are invariant, affine and exact
inverse images under every order transition. Thus the domains are coordinated
before any choice of invariant lifts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples FiniteRelationAffinePrincipalCore
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance coherentOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coherentOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coherentOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)

omit [QuasiCompact p] [IsLocallyNoetherian A] [LocallyQuasiFinite p] in
include ha in
/-- A fixed original principal parameter gives an affine domain at every ideal-power order. -/
theorem rankStagePrincipal_affine (k : ℕ) : IsAffineOpen
    ((rankThickening (Over.mk p) n k).basicOpen
      ((rankThickeningMap (Over.mk p) n k).appTop a)) := by
  rw [← Scheme.preimage_basicOpen_top]
  unfold rankThickeningMap
  rw [Scheme.Hom.comp_preimage]
  apply IsAffineOpen.preimage
  apply ((isAffineOpen_top A).basicOpen a).preimage_of_isOpenImmersion
  simpa only [Scheme.Opens.opensRange_ι] using ha

local instance coherentFirst_finite (k : ℕ) : IsFinite (rankStageFirst (p := p) n k) :=
  rankStageFirst_finite n k

/-- The affine invariant whole-orbit core of the same original parameter at order k. -/
def rankStageCore (k : ℕ) : (rankThickening (Over.mk p) n k).Opens :=
  core (p := rankStageFirst (p := p) n k) (q := rankStageSecond e n k)
    ((rankThickeningMap (Over.mk p) n k).appTop a) (rankStagePrincipal_affine n a ha k)

/-- Each coordinated domain is affine without assuming the whole stage affine. -/
theorem rankStageCore_affine (k : ℕ) : IsAffineOpen (rankStageCore e n a ha k) :=
  core_isAffine _ _

/-- Each coordinated domain retains every full relation arrow over its source. -/
theorem rankStageCore_invariant (k : ℕ) :
    rankStageFirst (p := p) n k ⁻¹ᵁ rankStageCore e n a ha k =
      rankStageSecond e n k ⁻¹ᵁ rankStageCore e n a ha k :=
  core_invariant (rankStageEquivalence e n k) _ _

/-- All ideal-power transitions preserve exactly the chosen affine invariant domains. -/
theorem rankStageCore_preimage {k l : ℕ} (h : k ≤ l) :
    rankStageTransition (Over.mk p) n h ⁻¹ᵁ rankStageCore e n a ha l =
      rankStageCore e n a ha k := by
  have hs : (rankStageTransition (Over.mk p) n h).appTop
      ((rankThickeningMap (Over.mk p) n l).appTop a) =
        (rankThickeningMap (Over.mk p) n k).appTop a := by
    change (rankStageTransition (Over.mk p) n h ≫
      rankThickeningMap (Over.mk p) n l).appTop a = _
    rw [rankStageTransition_map]
  have hs' : IsAffineOpen ((rankThickening (Over.mk p) n k).basicOpen
      ((rankStageTransition (Over.mk p) n h).appTop
        ((rankThickeningMap (Over.mk p) n l).appTop a))) := by
    rw [hs]
    exact rankStagePrincipal_affine n a ha k
  simpa only [rankStageCore, hs] using core_preimage (rankStageEquivalence e n l)
    (rankStageEquivalence e n k) (rankStageTransition (Over.mk p) n h)
    (rankStageRelationTransition (p := p) n h) (rankStageRelationTransition_isPullback n h)
    (rankStageRelationTransition_second e n h)
    ((rankThickeningMap (Over.mk p) n l).appTop a) (rankStagePrincipal_affine n a ha l) hs'

end FLT.Mazur.EquivalenceRelationOrderedFrames

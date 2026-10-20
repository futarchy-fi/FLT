/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalBoundaryCoefficients

/-!
# Core relation tests are the full original base change

The entire relation over a core is Cartesian over the original first endpoint.
Every original arrow whose first endpoint factors through the core therefore
has a canonical full core-relation lift. Both endpoint equations are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {D A T : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance coreCartesianOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coreCartesianOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coreCartesianOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (k : ℕ)
local notation "C" => rankStageCore e n a ha k
local notation "r" => (rankStageFirst (p := p) n k).resLE C _ le_rfl
local notation "s" => (rankStageSecond e n k).resLE C _
  (rankStageCore_invariant e n a ha k).le
local notation "f" => rankStageCoreOriginalMap e n a ha k
local notation "δ" => rankStageCoreOriginalArrow e n a ha k
attribute [local irreducible] rankStageCore

/-- The complete core relation is the Cartesian pullback of the original first endpoint. -/
theorem rankStageCoreOriginalArrow_isPullback : IsPullback δ r p f := by
  have H : IsPullback (rankStageFirst (p := p) n k ⁻¹ᵁ C).ι r
      (rankStageFirst (p := p) n k) (C).ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict _ _).flip
  exact H.paste_horiz (rankStageFirst_isPullback (p := p) n k)

/-- Full invariant values agree on any original arrow whose first endpoint lies in the core. -/
theorem rankStageCore_original_invariant_test (u : T ⟶ (C).toScheme) (z : T ⟶ D)
    (hz : z ≫ p = u ≫ f) (v : rankStageCoreInvariants e n a ha k) :
    ∃ u' : T ⟶ (C).toScheme, z ≫ q = u' ≫ f ∧ u.appTop v.val = u'.appTop v.val := by
  let H := rankStageCoreOriginalArrow_isPullback e n a ha k
  let t := H.lift z u hz
  have ht : t ≫ δ = z := H.lift_fst _ _ _
  have hu : t ≫ r = u := H.lift_snd _ _ _
  refine ⟨t ≫ s, ?_, ?_⟩
  · rw [Category.assoc, ← rankStageCoreOriginalArrow_second, ← Category.assoc, ht]
  · rw [← hu, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    exact congrArg t.appTop v.property

end FLT.Mazur.EquivalenceRelationOrderedFrames

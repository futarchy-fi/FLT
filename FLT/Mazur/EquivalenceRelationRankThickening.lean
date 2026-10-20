/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRankIdeal
public import FLT.Mazur.RelativeRankThickeningFinite

/-!
# Whole original equivalence relations on infinitesimal rank stages

Each stage carries the entire original relation, with both original endpoints
and a cartesian first-endpoint square. Its finite first projection and genuine
equivalence operations retain the complete ideal-power scheme structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] (e : CategoryTheory.EquivalenceRelation p q)
local instance rankStageOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankStageOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankStageOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n k : ℕ)
set_option quotPrecheck false
local notation "U" => rankImageOpen (Over.mk p) n
local notation "I" => rankStratumIdeal (Over.mk p) n ^ (k + 1)
local notation "j" => (I).subschemeι
local notation "r" => rankOpenFirst (p := p) n
local notation "s" => rankOpenSecond e n

omit [QuasiCompact p] in
/-- The first endpoint square retains the whole original relation over the rank open. -/
theorem rankOpenFirst_isPullback : IsPullback (p ⁻¹ᵁ U).ι r p (U).ι := by
  unfold rankOpenFirst
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict p U).flip

/-- Original reflexivity, inversion and composition on the whole rank-open relation. -/
def rankOpenEquivalence : CategoryTheory.EquivalenceRelation r s :=
  EquivalenceRelationFiber.invariantRestrictionEquivalence e
    (rankOpenFirst_isPullback (p := p) n)
    (Scheme.Hom.resLE_comp_ι q (rankImage_preimage_eq e n).le).symm

/-- The entire first-endpoint restriction to the actual ideal-power stage. -/
def rankStageRelation : Scheme := pullback r j

/-- Its full first projection to the unchanged rank thickening. -/
def rankStageFirst : rankStageRelation (p := p) n k ⟶ rankThickening (Over.mk p) n k :=
  pullback.snd r j

/-- Inclusion retains the complete original relation arrow. -/
def rankStageArrow : rankStageRelation (p := p) n k ⟶ D :=
  pullback.fst r j ≫ (p ⁻¹ᵁ U).ι

omit [QuasiCompact p] in
/-- The stage is the base change of the entire original first projection. -/
theorem rankStageFirst_isPullback : IsPullback (rankStageArrow (p := p) n k)
    (rankStageFirst (p := p) n k) p (rankThickeningMap (Over.mk p) n k) :=
  (IsPullback.of_hasPullback r j).paste_horiz (rankOpenFirst_isPullback (p := p) n)

instance rankStageFirst_etale : Etale (rankStageFirst (p := p) n k) :=
  MorphismProperty.of_isPullback (rankStageFirst_isPullback (p := p) n k)
    (inferInstanceAs (Etale p))

variable [IsLocallyNoetherian A]

/-- Exact rank-ideal invariance constructs the independent second endpoint. -/
def rankStageSecond : rankStageRelation (p := p) n k ⟶ rankThickening (Over.mk p) n k :=
  InvariantIdealRelation.snd I r s (rankIdeal_pow_invariant e n (k + 1))

/-- The second stage endpoint still maps to the independent original endpoint. -/
@[reassoc]
theorem rankStageSecond_map : rankStageSecond e n k ≫ rankThickeningMap (Over.mk p) n k =
    rankStageArrow (p := p) n k ≫ q := by
  change InvariantIdealRelation.snd I r s _ ≫ j ≫ (U).ι = _
  rw [← Category.assoc, InvariantIdealRelation.snd_ι, Category.assoc]
  change _ ≫ (q.resLE U _ (rankImage_preimage_eq e n).le ≫ (U).ι) = _
  rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc]
  rfl

instance rankStageSecond_etale : Etale (rankStageSecond e n k) := by
  unfold rankStageSecond
  infer_instance

/-- The actual full original equivalence relation on every infinitesimal rank stage. -/
def rankStageEquivalence : CategoryTheory.EquivalenceRelation
    (rankStageFirst (p := p) n k) (rankStageSecond e n k) :=
  InvariantIdealRelation.equivalence I (rankIdeal_pow_invariant e n (k + 1))
    (rankOpenEquivalence e n)

variable [LocallyQuasiFinite p]
local instance rankStageOver_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›

omit [IsLocallyNoetherian A] in
/-- The full original stage relation is finite, including over residual nonfinite points. -/
theorem rankStageFirst_finite : IsFinite (rankStageFirst (p := p) n k) := by
  let _ : IsFinite (pullback.snd p (rankThickeningMap (Over.mk p) n k)) :=
    finite_pullback_rankThickening (Over.mk p) n k
  rw [← (rankStageFirst_isPullback (p := p) n k).isoPullback_hom_snd]
  infer_instance

end FLT.Mazur.EquivalenceRelationOrderedFrames

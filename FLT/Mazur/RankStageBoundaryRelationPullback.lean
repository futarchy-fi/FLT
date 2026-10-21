/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryEndpointQuotient

/-!
# Full boundary-stage relations are original boundary pullbacks

The full finite-stage relation is Cartesian over the original first boundary
endpoint. Thus any original arrow whose prescribed endpoints factor through
the stage has a unique stage lift. The endpoint quotient equations are also
necessary, not just sufficient, for those fixed stage endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem kernel_le_of_factor {X Y T : Scheme.{0}}
    (c : X ⟶ Y) (d : T ⟶ X) (t : T ⟶ Y) (h : d ≫ c = t) :
    RingHom.ker c.appTop.hom ≤ RingHom.ker t.appTop.hom := by
  intro v hv
  change t.appTop v = 0
  rw [← h, Scheme.Hom.comp_appTop]
  change d.appTop (c.appTop v) = 0
  rw [show c.appTop v = 0 from hv, map_zero]

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance boundaryPullOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryPullOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryPullOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q) (k : ℕ)
set_option quotPrecheck false
local notation "C" => rankStageCore e n a ha k
local notation "r" => (rankStageFirst (p := p) n k).resLE C _ le_rfl
local notation "s" => (rankStageSecond e n k).resLE C _
  (rankStageCore_invariant e n a ha k).le
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J k
local notation "hI" => rankStageCoreBoundaryIdeal_invariant e n a ha J hJ k
local notation "rI" => pullback.snd r (I).subschemeι
local notation "sI" => InvariantIdealRelation.snd I r s hI
local notation "g" => rankStageCoreOriginalBoundaryMap e n a ha J k
local notation "δ" => rankStageOriginalBoundaryArrow e n a ha J k

/-- The full finite boundary relation is the original first-boundary pullback. -/
theorem rankStageOriginalBoundaryArrow_isPullback :
    IsPullback δ rI (pullback.snd p J.subschemeι) g := by
  have H := (IsPullback.of_hasPullback r (I).subschemeι).paste_horiz
    (rankStageCoreOriginalArrow_isPullback e n a ha k)
  have H' : IsPullback (δ ≫ pullback.fst p J.subschemeι) rI p (g ≫ J.subschemeι) := by
    simpa only [rankStageOriginalBoundaryArrow, pullback.lift_fst,
      rankStageCoreOriginalBoundaryMap, IdealSheafClosedTransitions.map_inclusion] using H
  exact H'.of_right (rankStageOriginalBoundaryArrow_first e n a ha J k)
    (IsPullback.of_hasPullback p J.subschemeι)

local instance originalBoundaryMap_mono : Mono g := by
  have H := IdealSheafClosedTransitions.isPullback I J
    (rankStageCoreOriginalMap e n a ha k) (rankStageCoreOriginalMap_ideal e n a ha J k)
  exact H.mono_snd_of_mono

include hJ in
/-- Any original arrow with both fixed stage endpoints lifts to the full finite stage relation. -/
theorem rankStage_boundary_arrow_lift {T : Scheme.{0}}
    (x y : T ⟶ (I).subscheme) (z : T ⟶ pullback p J.subschemeι)
    (hx : z ≫ pullback.snd p J.subschemeι = x ≫ g)
    (hy : z ≫ InvariantIdealRelation.snd J p q hJ = y ≫ g) :
    ∃ d : T ⟶ pullback r (I).subschemeι, d ≫ δ = z ∧ d ≫ rI = x ∧ d ≫ sI = y := by
  let H := rankStageOriginalBoundaryArrow_isPullback e n a ha J k
  let d := H.lift z x hx
  have hd : d ≫ δ = z := H.lift_fst _ _ _
  refine ⟨d, hd, H.lift_snd _ _ _, ?_⟩
  apply (cancel_mono g).mp
  rw [Category.assoc, ← rankStageOriginalBoundaryArrow_second e n a ha J hJ k,
    ← Category.assoc, hd, hy]

local notation "f" => rankStageBoundaryOriginalScalars e n a ha J k
local notation "h" => rankStageBoundaryOriginalScalars_condition e n a ha J hJ k
local notation "c" => pullback.lift rI sI h
attribute [local irreducible] rankStageBoundaryOriginalScalars

include hJ in
/-- For fixed stage endpoints the full quotient equations exactly detect original arrows. -/
theorem rankStage_boundary_quotient_iff_original_arrow {T : Scheme.{0}}
    (x y : T ⟶ (I).subscheme) (hxy : x ≫ f = y ≫ f) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker (pullback.lift x y hxy).appTop.hom ↔
      ∃ z : T ⟶ pullback p J.subschemeι,
        z ≫ pullback.snd p J.subschemeι = x ≫ g ∧
        z ≫ InvariantIdealRelation.snd J p q hJ = y ≫ g := by
  constructor
  · exact rankStage_original_boundary_arrow_of_quotient e n a ha J hJ k x y hxy
  · rintro ⟨z, hx, hy⟩
    obtain ⟨d, _, hd, hd'⟩ := rankStage_boundary_arrow_lift e n a ha J hJ k x y z hx hy
    have he : d ≫ c = pullback.lift x y hxy := by
      apply (IsPullback.of_hasPullback f f).hom_ext
      · simpa only [Category.assoc, pullback.lift_fst] using hd
      · simpa only [Category.assoc, pullback.lift_snd] using hd'
    exact kernel_le_of_factor c d (pullback.lift x y hxy) he

end FLT.Mazur.EquivalenceRelationOrderedFrames

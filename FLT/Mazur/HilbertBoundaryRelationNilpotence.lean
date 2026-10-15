/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryThickeningNilpotence
public import FLT.Mazur.NilpotentClosedRestriction

/-!
# Cartesian nilpotent transitions of the whole original relation

Both endpoint squares between infinitesimal orders are Cartesian. The relation
transitions are nilpotent closed immersions, with the same explicit exponent
as the source transition. No affineness of the relation is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "B" n:max => originalThickenedSource f hL d V c k n
local notation "i" n:max => originalThickenedSourceMap f hL d V c k n
local notation "C" n:max => originalThickenedRelation f hL d V c k n
local notation "r" n:max => originalThickenedFst f hL d V c k n
local notation "s" n:max => originalThickenedSnd f hL d V c k n
local notation "z" n:max => originalThickenedArrow f hL d V c k n
local notation "j" h:max => originalThickenedTransition f hL d V c k h
local notation "t" h:max => originalThickenedRelationTransition f hL d V c k h

omit [Etale V.hom] [IsAffine A.left] in
/-- Each full relation transition is the base change at the first endpoint. -/
theorem originalThickenedRelationTransition_fst_isPullback {m n : ℕ} (h : m ≤ n) :
    IsPullback (t h).left (r m).left (r n).left (j h).left := by
  apply IsPullback.of_right (h₁₂ := (z n).left) (h₂₂ := (i n).left)
    (v₁₃ := (fst f hL d V c k).left)
  · have H := originalThickenedFst_isPullback f hL d V c k m
    simpa only [← Over.comp_left, originalThickenedRelationTransition_arrow,
      originalThickenedTransition_source] using H
  · exact congrArg Over.Hom.left (originalThickenedRelationTransition_fst f hL d V c k h)
  · exact originalThickenedFst_isPullback f hL d V c k n

/-- The independent second endpoint also gives a Cartesian transition square. -/
theorem originalThickenedRelationTransition_snd_isPullback {m n : ℕ} (h : m ≤ n) :
    IsPullback (t h).left (s m).left (s n).left (j h).left := by
  apply IsPullback.of_right (h₁₂ := (z n).left) (h₂₂ := (i n).left)
    (v₁₃ := (snd f hL d V c k).left)
  · have H := originalThickenedSnd_isPullback f hL d V c k m
    simpa only [← Over.comp_left, originalThickenedRelationTransition_arrow,
      originalThickenedTransition_source] using H
  · exact congrArg Over.Hom.left (originalThickenedRelationTransition_snd f hL d V c k h)
  · exact originalThickenedSnd_isPullback f hL d V c k n

/-- Relation transitions are actual closed immersions of the nonaffine relation schemes. -/
instance originalThickenedRelationTransition_closed {m n : ℕ} (h : m ≤ n) :
    IsClosedImmersion (t h).left :=
  MorphismProperty.of_isPullback
    (originalThickenedRelationTransition_fst_isPullback f hL d V c k h).flip
    (inferInstanceAs (IsClosedImmersion (j h).left))

omit [Etale V.hom] [IsAffine A.left] in
/-- The entire relation kernel is the exact pulled-back source transition kernel. -/
theorem originalThickenedRelationTransition_ker {m n : ℕ} (h : m ≤ n) :
    (t h).left.ker = (j h).left.ker.comap (r n).left := by
  let H := originalThickenedRelationTransition_fst_isPullback f hL d V c k h
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

omit [Etale V.hom] in
/-- The original target-order exponent kills the full nonaffine relation kernel. -/
theorem originalThickenedRelationTransition_ker_pow {m n : ℕ} (h : m ≤ n) :
    (t h).left.ker ^ (n + 1) = ⊥ := by
  rw [originalThickenedRelationTransition_ker, ← AffineIdealPower.comap_pow,
    originalThickenedTransition_ker_pow, Scheme.IdealSheafData.comap_bot]

omit [Etale V.hom] in
/-- Whole original relation transitions are infinitesimal closed immersions. -/
theorem originalThickenedRelationTransition_nilpotent {m n : ℕ} (h : m ≤ n) :
    IsNilpotent (t h).left.ker :=
  ⟨n + 1, originalThickenedRelationTransition_ker_pow f hL d V c k h⟩

omit [Etale V.hom] in
/-- The relation tower retains every original point as well as its nilpotent data. -/
theorem originalThickenedRelationTransition_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (t h).left :=
  NilpotentClosedRestriction.surjective (t h).left
    (originalThickenedRelationTransition_nilpotent f hL d V c k h)

end FLT.Mazur.HilbertChart.AffineRestriction

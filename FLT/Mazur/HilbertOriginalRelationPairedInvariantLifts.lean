/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteTestInvariants
public import FLT.Mazur.HilbertOriginalRelationPairedAffineLifts

/-!
# Full invariant agreement on constructed residual relation charts

The two actual common-chart lifts have complete frames of the stage rank.
Their unchanged original arrow therefore equalizes every full invariant on
an affine etale neighborhood, with no reduction of the coefficient scheme.
This does not construct arrows for independent original scalar tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd
variable (n : ℕ) (o : Fin n)
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS

open RelativeOrderedTuples
local notation "endpoint" => F ≫ kS
local instance pairedInvariantStageOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance pairedInvariantStageOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance pairedInvariantStageOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- The actual residual relation charts equalize the entire fixed ring. -/
theorem exists_originalRelation_rankStage_invariant_lifts (m order : ℕ) (o' : Fin m)
    (z : rankPullbackThickening (Over.mk p) endpoint m order) :
    ∃ (W : (normalizedFullRelationFrames f hL d V c k m o').Opens)
      (T : Scheme.{0}) (a b : T ⟶ W.toScheme)
      (v : T ⟶ rankPullbackThickening (Over.mk p) endpoint m order) (t : T)
      (hW : ∀ g : Equiv.Perm (Fin m),
        (normalizedFullRelationAction f hL d V c k m o' g).hom ⁻¹ᵁ W = W),
      IsAffineOpen W ∧ IsAffine T ∧ Etale v ∧ v t = z ∧
      a ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
        v ≫ rankPullbackMap (Over.mk p) endpoint m order ≫ endpoint ∧
      b ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
        v ≫ rankPullbackMap (Over.mk p) endpoint m order ≫ H ≫ kS ∧
      ∀ s : invariantCoordinates
        (restrictedAction (normalizedFullRelationAction f hL d V c k m o') W hW),
        a.appTop s.val = b.appTop s.val := by
  obtain ⟨W, T, a, b, v, t, hWaff, hT, hv, ht, hW, ha, hb⟩ :=
    exists_originalRelation_rankStage_paired_affine f hL d V c k n o U m order o' z
  refine ⟨W, T, a, b, v, t, hW, hWaff, hT, hv, ht, ha, hb, ?_⟩
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let l := rankPullbackMap (Over.mk p) endpoint m order
  let δ := v ≫ l ≫ SchemeRelationRestriction.arrow p q kS
  have hp : δ ≫ p = a ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' := by
    dsimp only [δ]
    rw [Category.assoc, Category.assoc, SchemeRelationRestriction.arrow_fst, ha]
  have hq : δ ≫ q = b ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' := by
    dsimp only [δ]
    rw [Category.assoc, Category.assoc, SchemeRelationRestriction.arrow_snd, hb]
  apply invariant_eq_of_exactRank_original_arrow e m o' W hW a b δ hp hq
  change Set.range (a ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o') ⊆ _
  rw [ha]
  rintro _ ⟨w, rfl⟩
  exact rankPullback_endpoint (Over.mk p) endpoint m order (v w)

end FLT.Mazur.HilbertChart.AffineRestriction

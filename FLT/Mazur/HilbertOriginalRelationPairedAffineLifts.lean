/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationPairedRankStages
public import FLT.Mazur.HilbertPairedNormalizedAffineLifts
public import FLT.Mazur.HilbertSourceRelationRankStages

/-!
# Constructed paired frames on the full original residual relation

The actual arrow of the two-endpoint relation proves the missing second rank
condition. Its unsplit rank stages have common affine normalized frames at
all orders, including higher residual ranks. No scalar kernel-pair coverage
or agreement of all invariants is inferred from this construction.
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
local instance pairedHilbertStageOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance pairedHilbertStageOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance pairedHilbertStageOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- Every residual original relation stage has the same second endpoint rank. -/
theorem originalRelation_rankStage_second_exactRank (m order : ℕ) :
    Set.range (rankPullbackMap (Over.mk p) endpoint m order ≫ H ≫ kS) ⊆
      exactRank (Over.mk p) m :=
  SchemeRelationRestriction.rankPullback_second_exactRank e kS m order

/-- Both entire original endpoint sources are finite on the unsplit residual stage. -/
theorem originalRelation_rankStage_both_sources_finite (m order : ℕ) :
    IsFinite (pullback.snd p
      (rankPullbackMap (Over.mk p) endpoint m order ≫ endpoint)) ∧
    IsFinite (pullback.snd p
      (rankPullbackMap (Over.mk p) endpoint m order ≫ H ≫ kS)) := by
  let _ : LocallyQuasiFinite p :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
  exact SchemeRelationRestriction.rankPullback_both_sources_finite e kS m order

/-- Actual common affine frames on every full original relation stage need no rank assumption. -/
theorem exists_originalRelation_rankStage_paired_affine (m order : ℕ) (o' : Fin m)
    (z : rankPullbackThickening (Over.mk p) endpoint m order) :
    ∃ (W : (normalizedFullRelationFrames f hL d V c k m o').Opens)
      (T : Scheme.{0}) (a b : T ⟶ W.toScheme)
      (v : T ⟶ rankPullbackThickening (Over.mk p) endpoint m order) (t : T),
      IsAffineOpen W ∧ IsAffine T ∧ Etale v ∧ v t = z ∧
      (∀ g : Equiv.Perm (Fin m),
        (normalizedFullRelationAction f hL d V c k m o' g).hom ⁻¹ᵁ W = W) ∧
      a ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
        v ≫ rankPullbackMap (Over.mk p) endpoint m order ≫ endpoint ∧
      b ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
        v ≫ rankPullbackMap (Over.mk p) endpoint m order ≫ H ≫ kS := by
  exact exists_rankStage_paired_normalized_affine_lifts f hL d V c k m o'
    endpoint (H ≫ kS) order
    (originalRelation_rankStage_second_exactRank f hL d V c k n o U m order) z

end FLT.Mazur.HilbertChart.AffineRestriction

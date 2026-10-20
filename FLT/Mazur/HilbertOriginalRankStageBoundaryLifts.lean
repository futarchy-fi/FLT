/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOriginalRankStageCoverage
public import FLT.Mazur.RankStageAffineBoundaryLifts

/-!
# Full original boundary invariant lifts on every infinitesimal rank stage

Every original Hilbert source point lies under an affine invariant rank-stage
neighborhood whose full boundary section map is surjective. The entire original
relation and the pulled original boundary ideal are retained. Compatibility
and descent back through these nonflat stage maps remain separate obligations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
set_option quotPrecheck false
local notation "p" => (fst f hL d V c k).left
local notation "q" => (snd f hL d V c k).left
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence
  rankThickening rankThickeningMap rankStageFirst rankStageSecond rankStageBoundaryIdeal
  FiniteEtaleInvariantOpenBoundary.restriction SchemeOpenEnvelope.boundaryIdealSheaf
local instance boundaryLiftHilbert_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
local instance boundaryLiftHilbertOver_etale : Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)
local instance boundaryLiftHilbertOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance boundaryLiftHilbertOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "J" => SchemeOpenEnvelope.boundaryIdealSheaf π O

/-- Every original source point has a full-boundary lifting neighborhood on every stage order. -/
theorem exists_originalRankStage_boundary_lifting_neighborhood (powK : ℕ) (x : A.left) :
    let _ := selectedAffineHilbertSource_isNoetherian f d V k
    ∃ (n : ℕ) (y : rankThickening (Over.mk p) n powK)
      (U : (rankThickening (Over.mk p) n powK).Opens)
      (hU : rankStageFirst («p» := p) n powK ⁻¹ᵁ U = rankStageSecond e n powK ⁻¹ᵁ U),
      rankThickeningMap (Over.mk p) n powK y = x ∧ IsAffineOpen U ∧ y ∈ U ∧
      Function.Surjective (FiniteEtaleInvariantOpenBoundary.restriction
        (rankStageFirst («p» := p) n powK) (rankStageSecond e n powK) U hU
        (rankStageBoundaryIdeal («p» := p) n powK J)
        (originalRankStage_boundaryIdeal_invariant f hL d V c k n powK)) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  have h : p ≫ A.hom = q ≫ A.hom :=
    (fst f hL d V c k).w.trans (snd f hL d V c k).w.symm
  exact exists_rankStage_boundary_lifting_neighborhood e A.hom h J
    (SchemeOpenEnvelope.boundaryIdealSheaf_comap_eq π O p q
      (fullEnvelopeInterior_invariant f hL d V c k)) powK x

end FLT.Mazur.HilbertChart.AffineRestriction

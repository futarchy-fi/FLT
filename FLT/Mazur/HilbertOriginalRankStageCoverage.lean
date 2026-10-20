/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageAffineNeighborhoods
public import FLT.Mazur.RankStageBoundaryIdeal
public import FLT.Mazur.HilbertCompleteInteriorFiniteCriterion
public import FLT.Mazur.HilbertBoundaryClosedRelation

/-!
# Full original Hilbert relation coverage by infinitesimal affine rank stages

Every original source point, including residual nonfinite points, lifts to an
invariant affine open on an actual rank thickening. The relation on the stage
is the whole original pullback. The original boundary equations remain exactly
invariant there. This is locally closed coverage, not open or flat descent.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
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
local instance stageHilbert_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
local instance stageHilbertOver_etale : Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)
local instance stageHilbertOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance stageHilbertOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- Every original point lifts to an invariant affine neighborhood on a full finite rank stage. -/
theorem exists_originalRankStage_affine_lift (powK : ℕ) (x : A.left) :
    let _ := selectedAffineHilbertSource_isNoetherian f d V k
    ∃ (n : ℕ) (y : rankThickening (Over.mk p) n powK)
      (U : (rankThickening (Over.mk p) n powK).Opens),
      rankThickeningMap (Over.mk p) n powK y = x ∧ IsAffineOpen U ∧ y ∈ U ∧
      rankStageFirst («p» := p) n powK ⁻¹ᵁ U = rankStageSecond e n powK ⁻¹ᵁ U ∧
      IsFinite (rankStageFirst («p» := p) n powK) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  obtain ⟨n, y, U, hy, ha, hyU, hU⟩ := exists_rankStage_affine_lift e powK x
  exact ⟨n, y, U, hy, ha, hyU, hU, rankStageFirst_finite («p» := p) n powK⟩

local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "J" => SchemeOpenEnvelope.boundaryIdealSheaf π O

/-- The unchanged original boundary ideal is exactly invariant on every full rank stage. -/
theorem originalRankStage_boundaryIdeal_invariant (n powK : ℕ) :
    let _ := selectedAffineHilbertSource_isNoetherian f d V k
    (rankStageBoundaryIdeal («p» := p) n powK J).comap (rankStageFirst («p» := p) n powK) =
      (rankStageBoundaryIdeal («p» := p) n powK J).comap (rankStageSecond e n powK) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact rankStageBoundaryIdeal_invariant e n powK J
    (SchemeOpenEnvelope.boundaryIdealSheaf_comap_eq π O p q
      (fullEnvelopeInterior_invariant f hL d V c k))

end FLT.Mazur.HilbertChart.AffineRestriction

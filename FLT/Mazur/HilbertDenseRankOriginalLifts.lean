/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRankStratumOriginalNeighborhoods
public import FLT.Mazur.RelativeFrameDenseRankStrata

/-!
# Dense original orbit coverage by boundary lifting neighborhoods

The full Hilbert relation supplies a dense original open on which every point
has a neighborhood with surjective original boundary restriction. The remaining
closed locus has empty interior; coverage there is a separate problem.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "eo" => equivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local instance denseRankHilbertOver_etale : Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)
local instance denseRankHilbertOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance denseRankHilbertOver_quasiCompact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- The actual union of original orbit images of the constructed rank strata. -/
def rankStrataOrbitOpen : TopologicalSpace.Opens (Orbit eo) :=
  ⨆ n : ℕ, rankStratumOrbitOpen f hL d V c k n

/-- The constructed original orbit open is dense. -/
theorem rankStrataOrbitOpen_dense :
    Dense (rankStrataOrbitOpen f hL d V c k : Set (Orbit eo)) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  have hd := rankStrata_dense (Over.mk p)
  have hi := (projection_surjective eo).denseRange.dense_image (projection_continuous eo) hd
  apply hi.mono
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  change projection eo x ∈ ⨆ n : ℕ, rankStratumOrbitOpen f hL d V c k n
  exact (le_iSup (fun n ↦ rankStratumOrbitOpen f hL d V c k n) n)
    (show projection eo x ∈ rankStratumOrbitOpen f hL d V c k n from ⟨x, hn, rfl⟩)

/-- Every point in the dense original open has an actual original boundary lifting neighborhood. -/
theorem denseRank_original_lifting_neighborhood
    (W : TopologicalSpace.Opens (Orbit eo)) (x : Orbit eo) (hx : x ∈ W)
    (hr : x ∈ rankStrataOrbitOpen f hL d V c k) :
    ∃ O : TopologicalSpace.Opens (Orbit eo),
      O ≤ W ∧ x ∈ O ∧ Function.Surjective ((m).c.app (op O)) := by
  change x ∈ (⨆ n : ℕ, rankStratumOrbitOpen f hL d V c k n) at hr
  obtain ⟨n, hn⟩ := TopologicalSpace.Opens.mem_iSup.mp hr
  exact rankStratumOrbit_lifting_neighborhood f hL d V c k W n x hx hn

end FLT.Mazur.HilbertChart.AffineRestriction

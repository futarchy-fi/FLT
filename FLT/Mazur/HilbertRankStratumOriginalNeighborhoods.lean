/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRankStratumCover
public import FLT.Mazur.HilbertCompleteInteriorOriginalNeighborhoods

/-!
# Original boundary lifting neighborhoods on actual rank strata

Every point of an original rank stratum has an original orbit neighborhood
where all boundary sections lift. The neighborhood lies in any prescribed
original orbit domain. The rank stratum is constructed from the full relation.
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
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local instance rankHilbertOver_etale : Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)
local instance rankHilbertOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance rankHilbertOver_quasiCompact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- The actual original orbit image of the constructed rank stratum. -/
def rankStratumOrbitOpen (n : ℕ) : TopologicalSpace.Opens (Orbit eo) :=
  orbitImageOpen eo (q).isOpenMap (rankStratumOpen (Over.mk p) n)

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))

/-- Every original source point on the rank stratum has a genuine boundary lifting neighborhood. -/
theorem exists_rankStratum_original_lifting_neighborhood (n : ℕ) (x : A.left)
    (hx : x ∈ (pullOpen eo W).val)
    (hr : x ∈ rankStratumOpen (Over.mk p) n) :
    ∃ O : TopologicalSpace.Opens (Orbit eo),
      O ≤ W ∧ projection eo x ∈ O ∧ Function.Surjective ((m).c.app (op O)) := by
  obtain ⟨o, y, hy, hc⟩ := exists_rankStratum_interior_lift e n x hr
  have hw : normalizedFullRelationFirst f hL d V c k n o y ∈ (pullOpen eo W).val := by
    change first p q (Fin n) o y ∈ (pullOpen eo W).val
    rwa [hy]
  obtain ⟨O, hOW, hyO, hs⟩ :=
    exists_completeInterior_original_lifting_neighborhood f hL d V c k W n o y hw hc
  refine ⟨O, hOW, ?_, hs⟩
  change projection eo (first p q (Fin n) o y) ∈ O at hyO
  rwa [hy] at hyO

/-- Saturating the actual rank stratum preserves coverage by original lifting neighborhoods. -/
theorem rankStratumOrbit_lifting_neighborhood (n : ℕ) (x : Orbit eo)
    (hx : x ∈ W) (hr : x ∈ rankStratumOrbitOpen f hL d V c k n) :
    ∃ O : TopologicalSpace.Opens (Orbit eo),
      O ≤ W ∧ x ∈ O ∧ Function.Surjective ((m).c.app (op O)) := by
  obtain ⟨a, ha, rfl⟩ := hr
  exact exists_rankStratum_original_lifting_neighborhood f hL d V c k W n a hx ha

end FLT.Mazur.HilbertChart.AffineRestriction

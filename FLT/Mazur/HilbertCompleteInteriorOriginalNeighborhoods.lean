/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteChartBoundaryDescent

/-!
# Original lifting neighborhoods from complete interior frames

Every complete interior frame constructs a neighborhood in the actual original
orbit space, inside any prescribed original domain, on which EVERY boundary
section lifts. No coverage outside the complete interior is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
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
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W

/-- Interior frames give actual original neighborhoods with surjective boundary restriction. -/
theorem exists_completeInterior_original_lifting_neighborhood (n : ℕ) (o : Fin n)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hx : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val)
    (hc : x ∈ completeInterior («p» := p) («q» := q) (Fin n) o) :
    ∃ O : TopologicalSpace.Opens (Orbit eo),
      O ≤ W ∧ projection eo (normalizedFullRelationFirst f hL d V c k n o x) ∈ O ∧
      Function.Surjective ((m).c.app (op O)) := by
  obtain ⟨U, hU, hUW, ha, hxU, hcomplete, _⟩ :=
    exists_completeInterior_orbit_chart f hL d V c k W n o x hx hc
  let j := U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
  let O := orbitImageOpen eo (q).isOpenMap (etaleSourceImage j)
  refine ⟨O, ?_, ?_,
    completeChart_original_boundary_surjective f hL d V c k n o U hU hcomplete ha⟩
  · rintro y ⟨z, ⟨u, rfl⟩, rfl⟩
    exact hUW u.property
  · exact ⟨normalizedFullRelationFirst f hL d V c k n o x, ⟨⟨x, hxU⟩, rfl⟩, rfl⟩

end FLT.Mazur.HilbertChart.AffineRestriction

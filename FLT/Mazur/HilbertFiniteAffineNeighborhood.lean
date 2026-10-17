/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteInvariantAffineBasis

/-!
# Chosen finite affine neighborhoods in the original Hilbert orbit space

Each neighborhood is chosen from the proved norm-core construction. Its
membership, containment and affineness proofs are derived, so callers need
only supply an original point in the exact finite target locus.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
  (x : A.left) (hx : projection (equivalence f hL d V c k) x ∈ W)
  (hf : x ∈ finiteTargetOpen (Over.Hom.left (fst f hL d V c k)))

/-- An actual finite affine original orbit neighborhood, constructed by prime avoidance and norm. -/
def originalFiniteAffineNeighborhood : TopologicalSpace.Opens (Orbit e) :=
  (exists_originalFiniteAffine_neighborhood f hL d V c k W x hx hf).choose

/-- The constructed neighborhood contains the designated original point. -/
theorem mem_originalFiniteAffineNeighborhood :
    projection e x ∈ originalFiniteAffineNeighborhood f hL d V c k W x hx hf :=
  (exists_originalFiniteAffine_neighborhood f hL d V c k W x hx hf).choose_spec.1

/-- The constructed neighborhood refines the unchanged original section domain. -/
theorem originalFiniteAffineNeighborhood_le :
    originalFiniteAffineNeighborhood f hL d V c k W x hx hf ≤ W :=
  (exists_originalFiniteAffine_neighborhood f hL d V c k W x hx hf).choose_spec.2.1

/-- The whole source of the chosen original orbit neighborhood is affine. -/
theorem originalFiniteAffineNeighborhood_affine : IsAffineOpen
    (pullOpen e (originalFiniteAffineNeighborhood f hL d V c k W x hx hf)).val :=
  (exists_originalFiniteAffine_neighborhood f hL d V c k W x hx hf).choose_spec.2.2.1

/-- The whole original relation is finite over the chosen neighborhood. -/
theorem originalFiniteAffineNeighborhood_finite :
    (pullOpen e (originalFiniteAffineNeighborhood f hL d V c k W x hx hf)).val ≤
      finiteTargetOpen (p).left :=
  (exists_originalFiniteAffine_neighborhood f hL d V c k W x hx hf).choose_spec.2.2.2

end FLT.Mazur.HilbertChart.AffineRestriction

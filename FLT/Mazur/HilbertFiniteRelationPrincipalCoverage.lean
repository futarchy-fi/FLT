/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertProjectiveRelationPrincipalCoverage
public import FLT.Mazur.FiniteFlatGlobalSections

/-!
# Principal coverage from finiteness of the original Hilbert relation

The original first projection is étale. Its finiteness therefore supplies
finite-projective global sections and every original principal neighborhood.
No affine source or projectivity hypothesis needs to be supplied separately.
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
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
  originalBoundarySource originalBoundarySourceMap originalClosedRelation
  originalClosedFst originalClosedSnd originalClosedArrow originalClosedEquivalence
namespace OrbitBoundaryAtlas
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
attribute [local irreducible] EquivalenceRelationNormalizedFrames.action
  uniformSourceOpen orbitImageOpen etaleSourceImage
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Charts" => Chart f hL d V c k W

variable [IsFinite (Over.Hom.left (AffineRestriction.fst f hL d V c k))]

/-- The finite original projection gives full principal coverage through its étale geometry. -/
theorem uniformPrincipalCore_eq_of_finiteRelation :
    uniformPrincipalCore f hL d V c k W = W := by
  let _ : IsAffine (relation f hL d V c k).left := isAffine_of_isAffineHom p
  exact uniformPrincipalCore_eq_of_projective f hL d V c k W
    (p).finite_appTop (finiteFlat_appTop_projective p)

/-- Finiteness of the original projection makes the actual boundary scalar ideal the unit ideal. -/
theorem uniformPrincipalBoundaryIdeal_eq_top_of_finiteRelation
    (hW : IsAffineOpen (pullOpen eo W).val) :
    uniformPrincipalBoundaryIdeal f hL d V c k W = ⊤ := by
  apply (uniformPrincipalCore_boundary_cover_iff f hL d V c k W hW).mp
  rw [uniformPrincipalCore_eq_of_finiteRelation f hL d V c k W]

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction

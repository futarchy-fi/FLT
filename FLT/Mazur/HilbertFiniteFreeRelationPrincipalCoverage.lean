/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteRelationUniformCoverage
public import FLT.Mazur.HilbertUniformPrincipalCoreCoverage
public import FLT.Mazur.RelativeRelationNormPrincipal

/-!
# Principal coverage for an original relation with a genuine finite section basis

Whole-relation norms construct original invariant scalar neighborhoods inside
uniform chart images. A basis for the actual first projection proves finiteness,
so complete-lift coverage and principal coverage together give the source unit
ideal. No basis of a moving permutation relation is substituted.
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

variable [IsAffine (relation f hL d V c k).left]
  {ι : Type} [Finite ι]

omit [IsAffine V.left] [Etale V.hom] [IsOpenImmersion k.left] in
/-- A finite basis on the original affine relation proves the original projection finite. -/
theorem originalProjection_finite_of_basis :
    let _ := (p).appTop.hom.toAlgebra
    ∀ (_basis : Module.Basis ι Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤)),
      IsFinite p := by
  let _ := (p).appTop.hom.toAlgebra
  dsimp only
  intro basis
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr
  refine ⟨inferInstance, ?_⟩
  change Module.Finite Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤)
  exact Module.Finite.of_basis basis

/-- Every uniform chart point has an original scalar supported inside that chart image. -/
theorem uniformLiftingOpen_le_principalCore_of_basis :
    let _ := (p).appTop.hom.toAlgebra
    ∀ (_basis : Module.Basis ι Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤)),
      uniformLiftingOpen f hL d V c k W ≤ uniformPrincipalCore f hL d V c k W := by
  let _ := (p).appTop.hom.toAlgebra
  dsimp only
  intro basis x hx
  let _ := originalProjection_finite_of_basis f hL d V c k basis
  obtain ⟨a, ha⟩ := (mem_uniformLiftingOpen f hL d V c k W x).mp hx
  obtain ⟨s, hs, hsO⟩ := exists_invariantPrincipal_of_basis eo e W
    (uniformOrbitOpen f hL d V c k W a)
    (uniformOrbitOpen_le f hL d V c k W a) x ha basis
  exact (mem_uniformPrincipalCore f hL d V c k W x).mpr ⟨s, ⟨a, hsO⟩, hs⟩

/-- A genuine basis for the full original relation removes both coverage obstructions. -/
theorem uniformPrincipalCore_eq_of_basis :
    let _ := (p).appTop.hom.toAlgebra
    ∀ (_basis : Module.Basis ι Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤)),
      uniformPrincipalCore f hL d V c k W = W := by
  let _ := (p).appTop.hom.toAlgebra
  dsimp only
  intro basis
  let _ := originalProjection_finite_of_basis f hL d V c k basis
  apply le_antisymm
  · exact (uniformPrincipalCore_le_uniformLiftingOpen f hL d V c k W).trans
      (uniformLiftingOpen_le f hL d V c k W)
  · exact (uniformLiftingOpen_eq_of_finite f hL d V c k W).ge.trans
      (uniformLiftingOpen_le_principalCore_of_basis f hL d V c k W basis)

/-- The actual original boundary source ideal is the unit ideal in this finite-free case. -/
theorem uniformPrincipalBoundaryIdeal_eq_top_of_basis
    (hW : IsAffineOpen (pullOpen eo W).val) :
    let _ := (p).appTop.hom.toAlgebra
    ∀ (_basis : Module.Basis ι Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤)),
      uniformPrincipalBoundaryIdeal f hL d V c k W = ⊤ := by
  let _ := (p).appTop.hom.toAlgebra
  dsimp only
  intro basis
  apply (uniformPrincipalCore_boundary_cover_iff f hL d V c k W hW).mp
  rw [uniformPrincipalCore_eq_of_basis f hL d V c k W basis]

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction

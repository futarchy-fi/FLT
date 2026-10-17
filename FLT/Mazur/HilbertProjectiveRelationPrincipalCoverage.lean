/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteRelationUniformCoverage
public import FLT.Mazur.HilbertUniformPrincipalCoreCoverage
public import FLT.Mazur.RelativeRelationProjectiveNormPrincipal

/-!
# Original Hilbert principal coverage from finite-projective sections

Finite projectivity of the actual original first-projection algebra gives
invariant norm neighborhoods. Combining them with complete-interior coverage
proves the original boundary source scalar ideal is the unit ideal.
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

omit [IsAffine V.left] [Etale V.hom] [IsOpenImmersion k.left] in
/-- Finite original sections prove finiteness of the original projection. -/
theorem originalProjection_finite_of_sections :
    let _ := (p).appTop.hom.toAlgebra
    Module.Finite Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤) →
      IsFinite p := by
  let _ := (p).appTop.hom.toAlgebra
  dsimp only
  intro hf
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr
  refine ⟨inferInstance, ?_⟩
  change Module.Finite Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤)
  exact hf

/-- Every uniform chart point has an original scalar supported inside that chart image. -/
theorem uniformLiftingOpen_le_principalCore_of_projective :
    let _ := (p).appTop.hom.toAlgebra
    Module.Finite Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤) →
    Module.Projective Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤) →
      uniformLiftingOpen f hL d V c k W ≤ uniformPrincipalCore f hL d V c k W := by
  let _ := (p).appTop.hom.toAlgebra
  dsimp only
  intro hf hp x hx
  let _ := originalProjection_finite_of_sections f hL d V c k hf
  obtain ⟨a, ha⟩ := (mem_uniformLiftingOpen f hL d V c k W x).mp hx
  obtain ⟨s, hs, hsO⟩ := exists_invariantPrincipal_of_finite_projective eo e W
    (uniformOrbitOpen f hL d V c k W a)
    (uniformOrbitOpen_le f hL d V c k W a) x ha hf hp
  exact (mem_uniformPrincipalCore f hL d V c k W x).mpr ⟨s, ⟨a, hsO⟩, hs⟩

/-- Finite projectivity of the original relation removes both coverage obstructions. -/
theorem uniformPrincipalCore_eq_of_projective :
    let _ := (p).appTop.hom.toAlgebra
    Module.Finite Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤) →
    Module.Projective Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤) →
      uniformPrincipalCore f hL d V c k W = W := by
  let _ := (p).appTop.hom.toAlgebra
  dsimp only
  intro hf hp
  let _ := originalProjection_finite_of_sections f hL d V c k hf
  apply le_antisymm
  · exact (uniformPrincipalCore_le_uniformLiftingOpen f hL d V c k W).trans
      (uniformLiftingOpen_le f hL d V c k W)
  · exact (uniformLiftingOpen_eq_of_finite f hL d V c k W).ge.trans
      (uniformLiftingOpen_le_principalCore_of_projective f hL d V c k W hf hp)

/-- The actual original boundary source ideal is the unit ideal in this finite-projective case. -/
theorem uniformPrincipalBoundaryIdeal_eq_top_of_projective
    (hW : IsAffineOpen (pullOpen eo W).val) :
    let _ := (p).appTop.hom.toAlgebra
    Module.Finite Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤) →
    Module.Projective Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤) →
      uniformPrincipalBoundaryIdeal f hL d V c k W = ⊤ := by
  let _ := (p).appTop.hom.toAlgebra
  dsimp only
  intro hf hp
  apply (uniformPrincipalCore_boundary_cover_iff f hL d V c k W hW).mp
  rw [uniformPrincipalCore_eq_of_projective f hL d V c k W hf hp]

end OrbitBoundaryAtlas
end FLT.Mazur.HilbertChart.AffineRestriction

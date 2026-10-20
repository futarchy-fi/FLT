/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertWholeScalarFiniteCover
public import FLT.Mazur.SchemeScalarConstructibleImage

/-!
# Finite whole-complete chart covers for arbitrary original orbit domains

Compactness comes from the original selected Noetherian affine Hilbert source.
Scalar Noetherianity remains explicit; no affineness of the orbit domain is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => orbitScalarCoordinates eo W

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen

local notation "K" P => scalarResidueClosure P
local notation "t" P => Spec.map (CommRingCat.ofHom (algebraMap Ω (K P)))
attribute [local irreducible] scalarResidueClosureField scalarResidueClosureAlgebra

omit [IsAffine V.left] in
/-- Every original orbit source domain is compact, even when it is not affine. -/
theorem originalOrbitSource_compact : CompactSpace (E).toScheme := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  let _ : TopologicalSpace.NoetherianSpace A.left := inferInstance
  exact isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)

omit [IsAffine V.left] in
/-- The actual scalar image is constructible for every original orbit domain. -/
theorem originalScalarImage_constructible [IsNoetherianRing Ω] :
    IsConstructible (Set.range (scalarMorphism s)) := by
  let _ := originalOrbitSource_compact f hL d V c k W
  apply scalar_image_constructible_of_affineCover
  intro i
  let φ := ((E).toScheme.affineCover.f i).appTop.hom.comp s
  let _ := φ.toAlgebra
  exact Algebra.FinitePresentation.of_finiteType.mp
    (originalOrbitAffineCover_scalar_finiteType f hL d V c k W i)

/-- Finite actual whole-complete chart covers do not require an affine orbit domain. -/
theorem exists_finite_original_wholeScalar_cover_of_noetherian [IsNoetherianRing Ω] :
    ∃ charts : Finset (OriginalScalarAffineChart f hL d V c k W),
      (⋃ C ∈ charts, C.wholeLocus) = Set.range (scalarMorphism s) := by
  obtain ⟨charts, hc⟩ := ScalarConstructibleStrata.exists_finite_constructible_subcover
    (Set.range (scalarMorphism s)) (originalScalarImage_constructible f hL d V c k W)
    (fun C : OriginalScalarAffineChart f hL d V c k W ↦ C.wholeLocus)
    (fun C ↦ C.wholeLocus_constructible)
    (by rw [originalScalarAffineCharts_cover f hL d V c k W])
  refine ⟨charts, Set.Subset.antisymm ?_ hc⟩
  intro P hP
  obtain ⟨C, _, hC⟩ := Set.mem_iUnion₂.mp hP
  rw [← originalScalarAffineCharts_cover f hL d V c k W]
  exact Set.mem_iUnion.mpr ⟨C, hC⟩

end FLT.Mazur.HilbertChart.AffineRestriction

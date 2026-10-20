/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertWholeScalarImageCover
public import FLT.Mazur.ScalarConstructibleFiniteCover

/-!
# Finite actual chart covers of the original scalar image

Chart data consist only of a size, a distinguished label and an actual stable
affine open over the prescribed domain. Under explicit Noetherianity of the
original scalar ring, finitely many such charts cover the entire actual image
of an affine original domain by their whole complete scalar loci.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme] [TopologicalSpace.NoetherianSpace B.toScheme]
  {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))
attribute [local irreducible] source action restrictedAction

/-- Finite presentation makes the actual nonempty whole complete scalar locus constructible. -/
theorem wholeCompleteScalarLocus_constructible (hfp : σ.FinitePresentation) :
    IsConstructible (wholeCompleteScalarLocus e I o B hB σ) := by
  have hz : IsConstructible
      (completeAffineOrbitImage e I o B hB :
        Set (quotient (restrictedAction (action e I o) B hB))) := by
    rw [← completeAffineOrbitTests_zeroLocus]
    apply IsConstructible.of_compl
    have ht := PrimeSpectrum.isRetrocompact_zeroLocus_compl
      (completeAffineOrbitTests e I o B hB).finite_toSet
    exact ht.isConstructible (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  rw [wholeCompleteScalarLocus]
  exact (PrimeSpectrum.isConstructible_range_comap hfp).sdiff
    (PrimeSpectrum.isConstructible_comap_image hfp hz.compl)

end FLT.Mazur.EquivalenceRelationNormalizedFrames

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

/-- Actual stable affine chart data over the unchanged original orbit domain. -/
structure OriginalScalarAffineChart where
  /-- Number of distinct arrows in the original normalized frame. -/
  size : ℕ
  /-- Distinguished original frame coordinate. -/
  label : Fin size
  /-- The actual open subset of the original normalized frame scheme. -/
  domain : (normalizedFullRelationFrames f hL d V c k size label).Opens
  /-- Stability under the original endpoint-moving finite permutation action. -/
  stable : ∀ g : Equiv.Perm (Fin size),
    (normalizedFullRelationAction f hL d V c k size label g).hom ⁻¹ᵁ domain = domain
  /-- Every chart endpoint stays in the prescribed original orbit domain. -/
  overDomain : domain ≤ normalizedFullRelationFirst f hL d V c k size label ⁻¹ᵁ E
  /-- Affineness of this actual source open, without a completeness assumption. -/
  affine : IsAffineOpen domain

local notation "Chart" => OriginalScalarAffineChart f hL d V c k W

/-- The exact whole complete scalar locus of the displayed actual chart. -/
@[irreducible] def OriginalScalarAffineChart.wholeLocus (C : Chart) : Set (PrimeSpectrum Ω) :=
  let _ : IsAffine C.domain.toScheme := C.affine
  wholeCompleteScalarLocus e (Fin C.size) C.label C.domain C.stable
    (normalizedOriginalScalarMap f hL d V c k C.size C.label W
      C.domain C.stable C.overDomain)

/-- The family of actual charts covers precisely the actual original scalar image. -/
theorem originalScalarAffineCharts_cover :
    (⋃ C : Chart, C.wholeLocus) = Set.range (scalarMorphism s) := by
  rw [← originalWholeScalarChartLocus_eq_image f hL d V c k W]
  ext P
  simp only [Set.mem_iUnion, OriginalScalarAffineChart.wholeLocus,
    originalWholeScalarChartLocus, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C.size, C.label, C.domain, C.stable, C.overDomain, C.affine, hC⟩
  · rintro ⟨n, o, U, hU, hUW, ha, hP⟩
    exact ⟨⟨n, o, U, hU, hUW, ha⟩, hP⟩

/-- Original Noetherian scalars give constructibility of each exact whole complete chart locus. -/
theorem OriginalScalarAffineChart.wholeLocus_constructible [IsNoetherianRing Ω] (C : Chart) :
    IsConstructible C.wholeLocus := by
  let _ : IsAffine C.domain.toScheme := C.affine
  let _ := originalSource_affine_isNoetherian f hL d V c k C.size C.label C.domain C.affine
  rw [OriginalScalarAffineChart.wholeLocus]
  apply wholeCompleteScalarLocus_constructible
  exact normalizedChart_originalScalar_finitePresentation f hL d V c k W C.size C.label
    C.domain C.stable C.overDomain

/-- Finitely many actual charts suffice for the whole original affine-domain scalar image. -/
theorem exists_finite_original_wholeScalar_cover [IsNoetherianRing Ω] (hW : IsAffineOpen E) :
    ∃ charts : Finset Chart,
      (⋃ C ∈ charts, C.wholeLocus) = Set.range (scalarMorphism s) := by
  let _ : IsAffine (E).toScheme := hW
  have hfp : (s).FinitePresentation := by
    let _ := (s).toAlgebra
    exact Algebra.FinitePresentation.of_finiteType.mp
      (originalOrbitSource_scalar_finiteType f hL d V c k W hW)
  have himage : IsConstructible (Set.range (scalarMorphism s)) := by
    rw [scalarMorphism_range_eq_comap]
    exact PrimeSpectrum.isConstructible_range_comap hfp
  obtain ⟨charts, hc⟩ := ScalarConstructibleStrata.exists_finite_constructible_subcover
    (Set.range (scalarMorphism s)) himage (fun C : Chart ↦ C.wholeLocus)
    (fun C ↦ C.wholeLocus_constructible)
    (by rw [originalScalarAffineCharts_cover f hL d V c k W])
  refine ⟨charts, Set.Subset.antisymm ?_ hc⟩
  intro P hP
  rw [Set.mem_iUnion] at hP
  obtain ⟨C, hC⟩ := hP
  rw [Set.mem_iUnion] at hC
  rw [← originalScalarAffineCharts_cover f hL d V c k W]
  exact Set.mem_iUnion.mpr ⟨C, hC.choose_spec⟩

end FLT.Mazur.HilbertChart.AffineRestriction

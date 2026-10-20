/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRequiredScalarInfinitesimals
public import FLT.Mazur.SchemeConstructibleNoetherianPullback

/-!
# Finite whole-complete charts over every required boundary prime

The actual boundary source is Noetherian. Pulling chart loci back to that
source makes them constructible by finite type and base change. Compactness
then gives finitely many actual charts covering every boundary contraction.
No Noetherianity of the original invariant scalar ring is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeConstructibleNoetherianPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme] [TopologicalSpace.NoetherianSpace B.toScheme]
  {R T : Type} [CommRing R] [CommRing T] [IsNoetherianRing T]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))
  (κ : R →+* T)
attribute [local irreducible] source action restrictedAction

/-- Whole-complete loci become constructible over any Noetherian scalar test. -/
theorem wholeCompleteScalarLocus_noetherian_preimage (hft : σ.FiniteType) :
    IsConstructible (PrimeSpectrum.comap κ ⁻¹' wholeCompleteScalarLocus e I o B hB σ) := by
  have hz : IsConstructible
      (completeAffineOrbitImage e I o B hB :
        Set (quotient (restrictedAction (action e I o) B hB))) := by
    rw [← completeAffineOrbitTests_zeroLocus]
    apply IsConstructible.of_compl
    have ht := PrimeSpectrum.isRetrocompact_zeroLocus_compl
      (completeAffineOrbitTests e I o B hB).finite_toSet
    exact ht.isConstructible (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  let sf := Spec.map (CommRingCat.ofHom σ)
  let sg := Spec.map (CommRingCat.ofHom κ)
  let _ : LocallyOfFiniteType sf :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hft
  rw [wholeCompleteScalarLocus, Set.preimage_sdiff]
  exact (preimage_range_constructible sf sg).sdiff
    (preimage_image_constructible sf sg _ hz.compl)

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

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)
attribute [local irreducible] originalClosedEquivalence originalClosedInvariantMap
  originalClosedSectionPullback originalAmbientBoundaryRestriction

local notation "Chart" => OriginalScalarAffineChart f hL d V c k W

variable {f hL d V c k W}

/-- Constructibility is needed only on the unchanged Noetherian boundary source. -/
theorem OriginalScalarAffineChart.boundaryLocus_constructible (hW : IsAffineOpen E) (C : Chart) :
    IsConstructible (PrimeSpectrum.comap κ ⁻¹' C.wholeLocus) := by
  let _ := originalAmbientBoundary_noetherian f hL d V c k W hW
  let _ : IsAffine C.domain.toScheme := C.affine
  let _ := originalSource_affine_isNoetherian f hL d V c k C.size C.label C.domain C.affine
  rw [OriginalScalarAffineChart.wholeLocus]
  apply wholeCompleteScalarLocus_noetherian_preimage
  exact originalSource_invariantScalar_finiteType f hL d V c k C.size C.label W
    C.domain C.stable C.overDomain

variable (f hL d V c k W)

/-- Finitely many actual charts cover every required prime, without scalar Noetherianity. -/
theorem exists_finite_originalBoundary_wholeScalar_cover (hW : IsAffineOpen E) :
    ∃ charts : Finset Chart, ∀ P : PrimeSpectrum T,
      ∃ C ∈ charts, PrimeSpectrum.comap κ P ∈ C.wholeLocus := by
  obtain ⟨charts, hc⟩ := ScalarConstructibleStrata.exists_finite_constructible_subcover
    (Set.univ : Set (PrimeSpectrum T)) .univ
    (fun C : Chart ↦ PrimeSpectrum.comap κ ⁻¹' C.wholeLocus)
    (fun C ↦ C.boundaryLocus_constructible hW) (by
      intro P _
      obtain ⟨C, hC⟩ := exists_originalBoundaryPrime_wholeScalar_chart f hL d V c k W hW P
      exact Set.mem_iUnion.mpr ⟨C, hC⟩)
  refine ⟨charts, fun P ↦ ?_⟩
  obtain ⟨C, hC, hP⟩ := Set.mem_iUnion₂.mp (hc (Set.mem_univ P))
  exact ⟨C, hC, hP⟩

open ScalarPrimeThickenings

/-- One finite actual chart family supplies every required prime and all its local orders. -/
theorem exists_finite_originalBoundary_infinitesimal_cover (hW : IsAffineOpen E) :
    ∃ charts : Finset Chart, ∀ P : PrimeSpectrum T,
      ∃ C ∈ charts, PrimeSpectrum.comap κ P ∈ C.wholeLocus ∧
        ∀ order : ℕ, C.scalarTestEqualizes
          (Spec.map (CommRingCat.ofHom (primeThickeningMap (PrimeSpectrum.comap κ P) order))) := by
  obtain ⟨charts, hc⟩ := exists_finite_originalBoundary_wholeScalar_cover f hL d V c k W hW
  refine ⟨charts, fun P ↦ ?_⟩
  obtain ⟨C, hC, hP⟩ := hc P
  refine ⟨C, hC, hP, fun order ↦ C.scalarTestEqualizes_of_support _ ?_⟩
  intro x
  change PrimeSpectrum.comap (primeThickeningMap (PrimeSpectrum.comap κ P) order) x ∈ _
  rw [primeThickening_center]
  exact hP

end FLT.Mazur.HilbertChart.AffineRestriction

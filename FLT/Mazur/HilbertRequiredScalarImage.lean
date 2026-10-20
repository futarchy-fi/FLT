/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertWholeScalarFiniteCover
public import FLT.Mazur.HilbertBoundaryAmbientPresentation

/-!
# The original local cokernel primes lie in the actual scalar image

The required primes are contractions from the actual boundary source ring.
Its restriction map factors through the unchanged ambient source coordinates.
Affineness of that source domain gives an endpoint for every such contraction,
without assuming that the whole scalar spectrum is reached.
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

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)
attribute [local irreducible] originalClosedEquivalence originalClosedInvariantMap
  originalClosedSectionPullback originalAmbientBoundaryRestriction

omit [IsAffine V.left] in
/-- Every boundary-source prime contracts to the actual original scalar image. -/
theorem originalBoundaryPrime_mem_scalarImage (hW : IsAffineOpen E) (P : PrimeSpectrum T) :
    PrimeSpectrum.comap κ P ∈ Set.range (scalarMorphism s) := by
  let _ : IsAffine (E).toScheme := hW
  let r : Γ((E).toScheme, ⊤) →+* T :=
    (originalAmbientBoundaryRestriction f hL d V c k W).comp (E).topIso.hom.hom
  have hr : r.comp s = κ := by
    ext a
    simp only [r, orbitScalarCoordinates, RingHom.comp_apply]
    change originalAmbientBoundaryRestriction f hL d V c k W
      ((E).topIso.hom ((E).topIso.inv ((invariantInclusion eo).hom.app (op W) a))) = _
    rw [Iso.inv_hom_id_apply]
    exact originalAmbientBoundaryRestriction_invariant f hL d V c k W a
  rw [scalarMorphism_range_eq_comap, ← hr]
  exact ⟨PrimeSpectrum.comap r P, rfl⟩

omit [IsAffine V.left] in
/-- In particular, every maximal ideal required by the original local cokernel has an endpoint. -/
theorem originalLocalCokernelPrime_mem_scalarImage (hW : IsAffineOpen E)
    (P : Ideal T) [P.IsMaximal] :
    (⟨P.comap κ, inferInstance⟩ : PrimeSpectrum Ω) ∈ Set.range (scalarMorphism s) :=
  originalBoundaryPrime_mem_scalarImage f hL d V c k W hW ⟨P, inferInstance⟩

/-- Required original boundary primes have whole-complete charts with the same scalar prime. -/
theorem exists_originalBoundaryPrime_wholeScalar_chart (hW : IsAffineOpen E)
    (P : PrimeSpectrum T) :
    ∃ C : OriginalScalarAffineChart f hL d V c k W,
      PrimeSpectrum.comap κ P ∈ C.wholeLocus := by
  have h := originalBoundaryPrime_mem_scalarImage f hL d V c k W hW P
  rw [← originalScalarAffineCharts_cover f hL d V c k W] at h
  exact Set.mem_iUnion.mp h

end FLT.Mazur.HilbertChart.AffineRestriction

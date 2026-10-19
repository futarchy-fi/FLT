/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOriginalScalarMaximalCover
public import FLT.Mazur.SchemeScalarResidueImage

/-!
# Exact coverage by whole complete original scalar charts

The union of the whole complete loci of actual stable affine charts equals
the entire actual scalar image of any original orbit domain. This
includes all its boundary points; primes outside that image are not covered.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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

/-- The scalar primes reached by a whole complete fiber in some actual original chart. -/
@[irreducible] def originalWholeScalarChartLocus : Set (PrimeSpectrum Ω) :=
  {P | ∃ (n : ℕ) (o : Fin n)
    (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
    (hU : ∀ g : Equiv.Perm (Fin n),
      (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E)
    (ha : IsAffineOpen U),
    let _ : IsAffine U.toScheme := ha
    P ∈ wholeCompleteScalarLocus e (Fin n) o U hU
      (normalizedOriginalScalarMap f hL d V c k n o W U hU hUW)}

/-- Every covered prime comes from an actual original endpoint, without enlarging the image. -/
theorem originalWholeScalarChartLocus_subset_image :
    originalWholeScalarChartLocus f hL d V c k W ⊆ Set.range (scalarMorphism s) := by
  intro P hP
  rw [originalWholeScalarChartLocus] at hP
  obtain ⟨n, o, U, hU, hUW, ha, hP⟩ := hP
  let _ : IsAffine U.toScheme := ha
  let ρ := restrictedAction (normalizedFullRelationAction f hL d V c k n o) U hU
  let σ := normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
  obtain ⟨⟨Q, hQ⟩, _⟩ := (mem_wholeCompleteScalarLocus_iff e (Fin n) o U hU σ P).mp hP
  obtain ⟨x, hx⟩ := (quotientMap ρ).surjective Q
  let j := (normalizedFullRelationFirst f hL d V c k n o).resLE E U hUW
  refine ⟨j x, ?_⟩
  have hf := normalizedSource_scalarMorphism_factor f hL d V c k W n o U hU hUW
  rw [scalarMorphism_through_quotient] at hf
  change (j ≫ scalarMorphism s) x = P
  rw [← hf]
  change PrimeSpectrum.comap σ (quotientMap ρ x) = P
  rwa [hx]

omit [IsAffine V.left] [IsAffine A.left] in
/-- Each original affine source neighborhood is finite type over the unchanged scalar ring. -/
theorem originalOrbitAffineCover_scalar_finiteType (i : (E).toScheme.affineCover.I₀) :
    (((E).toScheme.affineCover.f i).appTop.hom.comp s).FiniteType := by
  let _ : LocallyOfFiniteType A.hom := by
    rw [← k.w]
    infer_instance
  let _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let g := (E).toScheme.affineCover.f i ≫ (E).ι ≫ A.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
  let _ : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  let _ := integerCoordinates_finiteType g
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℤ Ω)
  have he : (((E).toScheme.affineCover.f i).appTop.hom.comp s).comp (algebraMap ℤ Ω) =
      algebraMap ℤ Γ((E).toScheme.affineCover.X i, ⊤) := Subsingleton.elim _ _
  rw [he]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- Whole complete charts exhaust exactly the actual scalar image of every original domain. -/
theorem originalWholeScalarChartLocus_eq_image :
    originalWholeScalarChartLocus f hL d V c k W = Set.range (scalarMorphism s) := by
  apply Set.Subset.antisymm (originalWholeScalarChartLocus_subset_image f hL d V c k W)
  intro P hP
  obtain ⟨b, hb⟩ := exists_scalar_residue_endpoint_of_affineCover s P
    (originalOrbitAffineCover_scalar_finiteType f hL d V c k W) hP
  rw [originalWholeScalarChartLocus]
  exact exists_original_wholeScalar_chart f hL d V c k W P b hb

end FLT.Mazur.HilbertChart.AffineRestriction

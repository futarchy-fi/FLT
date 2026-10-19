/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteInteriorCharts
public import FLT.Mazur.RelativeRelationMinimalScalarEndpoints
public import FLT.Mazur.EquivalenceRelationFiniteCompleteInterior
public import FLT.Mazur.SchemeFiniteGroupQuotientFiniteType

/-!
# Complete charts over prescribed minimal original scalar primes

The full original invariant domain supplies every minimal scalar prime with a
complete stable affine chart. Its endpoint has the unchanged scalar prime.
The chart size is constructed here;
no claim about a separately prescribed size or arbitrary scalar primes is made.
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
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsLocallyNoetherian A.left]
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

omit [IsAffine V.left] [IsAffine A.left] [IsLocallyNoetherian A.left] in
/-- The full original source coordinates are finite type over the prescribed invariant scalars. -/
theorem originalOrbitSource_scalar_finiteType (hW : IsAffineOpen E) : (s).FiniteType := by
  let _ : IsAffine (E).toScheme := hW
  let _ : LocallyOfFiniteType A.hom := by
    rw [← k.w]
    infer_instance
  let _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let g := (E).ι ≫ A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
  let _ : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  let _ := integerCoordinates_finiteType g
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℤ Ω)
  have he : (s).comp (algebraMap ℤ Ω) = algebraMap ℤ Γ((E).toScheme, ⊤) :=
    Subsingleton.elim _ _
  rw [he]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen

/-- Every minimal prime of the prescribed scalar domain has a complete affine chart above it. -/
theorem exists_original_minimal_scalar_complete_chart (hW : IsAffineOpen E)
    (P : PrimeSpectrum Ω)
    (hP : P.asIdeal ∈ minimalPrimes Ω) :
    ∃ (a : (E).toScheme) (n : ℕ) (o : Fin n)
      (x : normalizedFullRelationFrames f hL d V c k n o)
      (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (_hU : ∀ g : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
      (_hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E),
      scalarMorphism s a = P ∧
      normalizedFullRelationFirst f hL d V c k n o x = (E).ι a ∧
      IsAffineOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o := by
  let _ := QuasiCompactEtaleGeometricSections.locallyQuasiFinite p
  obtain ⟨a, ha, hf⟩ := exists_minimal_scalar_finite_endpoint eo W hW P hP
  obtain ⟨n, o, x, hx, hi⟩ := exists_complete_interior_lift_of_finiteTarget e ((E).ι a) hf
  have hxE : normalizedFullRelationFirst f hL d V c k n o x ∈ E := by
    change first p q (Fin n) o x ∈ E
    rw [hx]
    exact a.property
  obtain ⟨U, hU, hUW, hA, hxU, hC, _⟩ :=
    exists_completeInterior_orbit_chart f hL d V c k W n o x hxE hi
  exact ⟨a, n, o, x, U, hU, hUW, ha, hx, hA, hxU, hC⟩

end FLT.Mazur.HilbertChart.AffineRestriction

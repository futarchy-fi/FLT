/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryFlatIntegralTests

/-!
# Finite polynomial tests on arbitrary scalar branches

The full boundary tensor principal charts have finite type over any scalar
extension. Their finite generators are constructed before selecting a prime.
Polynomial relations with avoiding leading coefficients construct the exact
branch power equations; no branch power annihilation is taken as input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarTestLocalization OriginalPrimeIntegralFiber SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
/-- Keep the full original boundary scalar action in the tensor product. -/
local instance boundaryFlatGeneratorAlgebra : Algebra T C := (boundaryScalarHom s κ).toAlgebra

/-- The full boundary coordinate algebra has finite type over the unchanged boundary scalars. -/
theorem boundaryScalarHom_finiteType (hs : s.FiniteType) : (boundaryScalarHom s κ).FiniteType := by
  let _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom s)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hs
  let _ : LocallyOfFiniteType (boundaryScalarProjection s κ) := by
    dsimp only [boundaryScalarProjection, boundaryProduct]
    exact MorphismProperty.pullback_snd (P := @LocallyOfFiniteType)
      (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom κ)) inferInstance
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
    (φ := CommRingCat.ofHom (boundaryScalarHom s κ))).mp
  have he : Spec.map (CommRingCat.ofHom (boundaryScalarHom s κ)) =
      inv (boundaryProduct s κ).toSpecΓ ≫ boundaryScalarProjection s κ := by
    rw [← scalarMorphism_boundaryScalarHom, scalarMorphism, IsIso.inv_hom_id_assoc]
  rw [he]
  infer_instance

attribute [local irreducible] boundaryProduct

variable (S : Type) [CommRing S] [Algebra T S]
local notation "C'" => S ⊗[T] C
local notation "j" => Algebra.TensorProduct.includeRight (R := T) (A := S) (B := C)
local notation "E" t => Localization.Away (j (boundaryCoordinate s κ t))

/-- Arbitrary scalar extension preserves finite type of every full principal test chart. -/
theorem boundaryFlatTestScalar_finiteType (hs : s.FiniteType) (t : B) :
    (boundaryFlatTestScalar s κ S t).FiniteType := by
  let _ : Algebra.FiniteType T C :=
    RingHom.finiteType_algebraMap.mp (boundaryScalarHom_finiteType s κ hs)
  let _ : Algebra.FiniteType S C' := inferInstance
  exact (RingHom.finiteType_algebraMap.mpr
    (inferInstance : Algebra.FiniteType C' (E t))).comp
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType S C'))

/-- Finite branch generators chosen independently of any scalar prime. -/
def boundaryFlatTestGenerators (hs : s.FiniteType) (t : B) : Finset (E t) :=
  (finiteType_exists_scalar_generators _ (boundaryFlatTestScalar_finiteType s κ S hs t)).choose

/-- These are generators of the entire branch principal chart, including its nilpotents. -/
theorem boundaryFlatTestGenerators_generate (hs : s.FiniteType) (t : B) :
    Subring.closure (Set.range (boundaryFlatTestScalar s κ S t) ∪
      (boundaryFlatTestGenerators s κ S hs t : Set (E t))) = ⊤ :=
  (finiteType_exists_scalar_generators _
    (boundaryFlatTestScalar_finiteType s κ S hs t)).choose_spec

/-- Finite branch polynomial equations construct the full tensor power equations. -/
theorem boundary_tensor_equations_of_generator_polynomials (hs : s.FiniteType)
    (a : Finset B) (Q : PrimeSpectrum S)
    (hg : ∀ t ∈ a, ∀ x ∈ boundaryFlatTestGenerators s κ S hs t,
      ∃ p : Polynomial S, p.eval₂ (boundaryFlatTestScalar s κ S t) x = 0 ∧
        p.leadingCoeff ∉ Q.asIdeal)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z =
      PrimeSpectrum.comap (algebraMap T S) Q →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    ∀ t ∈ a, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
      boundaryTensorPowerEquation s κ S t x k := by
  apply boundary_tensor_equations_of_integral_tests s κ S a Q _ hf
  intro t ht
  exact localizedMap_integral_of_generator_equations _ Q.asIdeal
    (boundaryFlatTestGenerators s κ S hs t : Set (E t))
    (boundaryFlatTestGenerators_generate s κ S hs t) (hg t ht)

end FLT.Mazur.AffineScalarBoundaryNilpotence

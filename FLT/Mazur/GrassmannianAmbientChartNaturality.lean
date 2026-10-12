/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientCoordinateMap

/-!
# Naturality of the ambient affine chart representation

Precomposition of the classifying scheme morphism corresponds to the actual
Grassmannian functor map for every coefficient algebra homomorphism. The inverse
classification is natural as well, by injectivity of the point equivalence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B M κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- Actual precomposition of a base-preserving affine chart morphism. -/
def splitChartSchemePointMap (f : A →ₐ[R] B)
    (p : {p : Spec (.of A) ⟶ splitChartScheme R κ d //
      p ≫ splitChartStructure R κ d = Spec.algebraMap R A}) :
    {p : Spec (.of B) ⟶ splitChartScheme R κ d //
      p ≫ splitChartStructure R κ d = Spec.algebraMap R B} := by
  refine ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫ p.val, ?_⟩
  rw [Category.assoc, p.property]
  rw [Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1
  exact ConcreteCategory.hom_ext _ _ f.commutes

omit [Fintype κ] in
/-- Precomposition corresponds to composition of polynomial classifying algebra maps. -/
theorem splitChartSchemePointMap_algHom (f : A →ₐ[R] B)
    (p : {p : Spec (.of A) ⟶ splitChartScheme R κ d //
      p ≫ splitChartStructure R κ d = Spec.algebraMap R A}) :
    Spec.homEquivAlgHom (splitChartSchemePointMap f p) =
      f.comp (Spec.homEquivAlgHom p) := by
  dsimp only [splitChartScheme] at p
  apply AlgHom.ext
  intro x
  change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ p.val)).hom x =
    f ((Spec.preimage p.val).hom x)
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

/-- Affine chart classification is natural with respect to every coefficient algebra map. -/
theorem ambientChartSchemePointEquiv_natural (f : A →ₐ[R] B)
    (i : AmbientChartIndex R M κ d)
    (p : {p : Spec (.of A) ⟶ splitChartScheme R κ d //
      p ≫ splitChartStructure R κ d = Spec.algebraMap R A}) :
    ambientChartSchemePointEquiv i (splitChartSchemePointMap f p) =
      ambientChartMap f i (ambientChartSchemePointEquiv i p) := by
  classical
  change ambientPointOfCoordinates i (Matrix.toLin'
    (matrixPolynomialHomEquiv R B κ d (Spec.homEquivAlgHom (splitChartSchemePointMap f p)))) =
      ambientChartMap f i (ambientPointOfCoordinates i (Matrix.toLin'
        (matrixPolynomialHomEquiv R A κ d (Spec.homEquivAlgHom p))))
  rw [splitChartSchemePointMap_algHom, ambientChartMap_ofCoordinates]
  rfl

/-- The unique classifying morphisms themselves commute with coefficient base change. -/
theorem ambientChartSchemePointEquiv_symm_natural (f : A →ₐ[R] B)
    (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    (ambientChartSchemePointEquiv i).symm (ambientChartMap f i N) =
      splitChartSchemePointMap f ((ambientChartSchemePointEquiv i).symm N) := by
  apply (ambientChartSchemePointEquiv i).injective
  rw [Equiv.apply_symm_apply, ambientChartSchemePointEquiv_natural, Equiv.apply_symm_apply]

/-- Forgetting chart membership gives naturality for the original Grassmannian functor. -/
theorem ambientChartSchemePointEquiv_natural_val (f : A →ₐ[R] B)
    (i : AmbientChartIndex R M κ d)
    (p : {p : Spec (.of A) ⟶ splitChartScheme R κ d //
      p ≫ splitChartStructure R κ d = Spec.algebraMap R A}) :
    (ambientChartSchemePointEquiv i (splitChartSchemePointMap f p)).val =
      Module.Grassmannian.map f (ambientChartSchemePointEquiv i p).val := by
  exact congrArg Subtype.val (ambientChartSchemePointEquiv_natural f i p)

end FLT.Mazur.GrassmannianChart

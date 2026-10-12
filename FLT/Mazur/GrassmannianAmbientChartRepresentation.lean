/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartPoints
public import FLT.Mazur.GrassmannianFunctorLocalizedChart
public import FLT.Mazur.GrassmannianSplitChartScheme

/-!
# Affine chart representation of original ambient quotient points

Each original-base chart represents exactly the original ambient quotient points
whose selected summand is a basis. Every Grassmannian point has such a classifying
morphism on a coefficient principal neighborhood of each prime. Compatibility on
overlaps and the global scheme representation are separate remaining steps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- The affine chart classifies original ambient quotients with the selected quotient basis. -/
def ambientChartSchemePointEquiv (i : AmbientChartIndex R M κ d) :
    {f : Spec (.of A) ⟶ splitChartScheme R κ d //
      f ≫ splitChartStructure R κ d = Spec.algebraMap R A} ≃
        AmbientChartPoint (ambientChartBaseChange A i) :=
  (splitChartSchemePointEquiv R κ d A).trans
    (ambientChartPointEquiv (ambientChartBaseChange A i))

/-- Each original ambient chart point has a unique base-preserving classifying morphism. -/
theorem ambientChartSchemePoint_unique (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    ∃! f : {f : Spec (.of A) ⟶ splitChartScheme R κ d //
        f ≫ splitChartStructure R κ d = Spec.algebraMap R A},
      ambientChartSchemePointEquiv i f = N :=
  (ambientChartSchemePointEquiv i).bijective.existsUnique N

/-- Every original quotient point is represented by an actual chart morphism near each prime. -/
theorem exists_local_ambient_classifying_map {ι : Type u} [Fintype ι]
    (b : Module.Basis ι R M) (N : Module.Grassmannian A (A ⊗[R] M) d)
    (hκ : Fintype.card κ = Fintype.card ι - d) (p : PrimeSpectrum A) :
    ∃ (i : AmbientChartIndex R M κ d) (r : A), r ∉ p.asIdeal ∧
      ∃ f : {f : Spec (.of (Localization.Away r)) ⟶ splitChartScheme R κ d //
        f ≫ splitChartStructure R κ d = Spec.algebraMap R (Localization.Away r)},
        (ambientChartSchemePointEquiv i f).val = Module.Grassmannian.map
          (IsScalarTower.toAlgHom R A (Localization.Away r)) N := by
  obtain ⟨i, r, hr, hi⟩ := exists_functor_localized_chart b N hκ p
  let C : AmbientChartPoint (ambientChartBaseChange (Localization.Away r) i) := ⟨_, hi⟩
  refine ⟨i, r, hr, (ambientChartSchemePointEquiv i).symm C, ?_⟩
  exact congrArg Subtype.val ((ambientChartSchemePointEquiv i).apply_symm_apply C)

end FLT.Mazur.GrassmannianChart

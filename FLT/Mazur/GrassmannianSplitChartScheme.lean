/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianChartPolynomialParameters
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Affine schemes representing split Grassmannian charts

The spectrum of the polynomial algebra in the complementary matrix entries
represents the split chart on affine test schemes over the original base. This
constructs the chart schemes; their open overlaps and gluing are separate work.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable (R : Type u) [CommRing R] (ι : Type u) (d : ℕ)

/-- The actual affine scheme of complementary matrix entries. -/
def splitChartScheme : Scheme.{u} := Spec (.of (MvPolynomial (Fin d × ι) R))

/-- Its original coefficient-base structure morphism. -/
def splitChartStructure : splitChartScheme R ι d ⟶ Spec (.of R) :=
  Spec.algebraMap R (MvPolynomial (Fin d × ι) R)

instance : IsAffine (splitChartScheme R ι d) := inferInstanceAs (IsAffine (Spec _))

/-- The chart coordinate algebra is finitely presented over the original coefficient base. -/
theorem splitChartRing_finitePresentation [Finite ι] :
    Algebra.FinitePresentation R (MvPolynomial (Fin d × ι) R) := inferInstance

instance [Finite ι] : LocallyOfFinitePresentation (splitChartStructure R ι d) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact (RingHom.finitePresentation_algebraMap).mpr
    (splitChartRing_finitePresentation R ι d)

variable [Fintype ι] (S : Type u) [CommRing S] [Algebra R S]

/-- Base-preserving maps into the affine chart classify the actual split quotient points. -/
def splitChartSchemePointEquiv :
    {f : Spec (.of S) ⟶ splitChartScheme R ι d //
      f ≫ splitChartStructure R ι d = Spec.algebraMap R S} ≃
        SplitChart S (ι → S) d :=
  Spec.homEquivAlgHom.trans (splitChartPolynomialEquiv R S ι d)

/-- Every split quotient point has a unique base-preserving classifying scheme morphism. -/
theorem splitChartSchemePoint_unique (N : SplitChart S (ι → S) d) :
    ∃! f : {f : Spec (.of S) ⟶ splitChartScheme R ι d //
        f ≫ splitChartStructure R ι d = Spec.algebraMap R S},
      splitChartSchemePointEquiv R ι d S f = N :=
  (splitChartSchemePointEquiv R ι d S).bijective.existsUnique N

/-- Equal represented scheme points have equal full original quotient relation submodules. -/
theorem splitChartSchemePoint_relations (f g : {f : Spec (.of S) ⟶ splitChartScheme R ι d //
    f ≫ splitChartStructure R ι d = Spec.algebraMap R S})
    (h : (splitChartSchemePointEquiv R ι d S f).val.toSubmodule =
      (splitChartSchemePointEquiv R ι d S g).val.toSubmodule) : f = g := by
  apply (splitChartSchemePointEquiv R ι d S).injective
  apply Subtype.ext
  exact Module.Grassmannian.ext h

end FLT.Mazur.GrassmannianChart

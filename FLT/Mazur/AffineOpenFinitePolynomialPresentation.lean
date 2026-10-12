/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenQuotientPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite polynomial coordinates on actual affine ambient opens

Local finite type supplies finitely many variables for the actual section ring.
The kernel is retained in full; its quotient is the original coefficient algebra.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
  [LocallyOfFiniteType z] (U : Z.affineOpens)

/-- The coefficient algebra of an actual affine open is of finite type. -/
theorem affineOpenCoefficient_finiteType :
    let _ := affineOpenCoefficientAlgebra z U
    Algebra.FiniteType R Γ(Z, U.val) := by
  change (Spec.preimage (U.property.fromSpec ≫ z)).hom.FiniteType
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
  rw [Spec.map_preimage]
  infer_instance


/-- A finite list of generators for the full actual section algebra. -/
def affineOpenFiniteGenerators : Finset Γ(Z, U.val) :=
  let _ := affineOpenCoefficientAlgebra z U
  (Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (affineOpenCoefficient_finiteType z U)).choose

/-- The finite variable type lives in the same universe as the actual ambient. -/
abbrev AffineOpenFiniteVars := {x // x ∈ affineOpenFiniteGenerators z U}

/-- The chosen surjection evaluates finite polynomial coordinates in the section algebra. -/
def affineOpenFiniteEvaluation :
    let _ := affineOpenCoefficientAlgebra z U
    MvPolynomial (AffineOpenFiniteVars z U) R →ₐ[R] Γ(Z, U.val) :=
  let _ := affineOpenCoefficientAlgebra z U
  (Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (affineOpenCoefficient_finiteType z U)).choose_spec.choose

/-- Every actual section has a finite-coordinate polynomial representative. -/
theorem affineOpenFiniteEvaluation_surjective :
    Function.Surjective (affineOpenFiniteEvaluation z U) :=
  let _ := affineOpenCoefficientAlgebra z U
  (Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (affineOpenCoefficient_finiteType z U)).choose_spec.choose_spec

/-- All relations of the finite coordinate presentation, including nonreduced structure. -/
def affineOpenFiniteRelations : Ideal (MvPolynomial (AffineOpenFiniteVars z U) R) :=
  let _ := affineOpenCoefficientAlgebra z U
  RingHom.ker (affineOpenFiniteEvaluation z U).toRingHom

/-- The full quotient is the original affine-open algebra over the original base. -/
def affineOpenFiniteQuotientEquiv :
    let _ := affineOpenCoefficientAlgebra z U
    (MvPolynomial (AffineOpenFiniteVars z U) R ⧸ affineOpenFiniteRelations z U) ≃ₐ[R]
      Γ(Z, U.val) :=
  let _ := affineOpenCoefficientAlgebra z U
  Ideal.quotientKerAlgEquivOfSurjective (affineOpenFiniteEvaluation_surjective z U)

end FLT.Mazur.HilbertChart

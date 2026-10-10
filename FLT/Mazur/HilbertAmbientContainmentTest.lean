/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealContainment
public import FLT.Mazur.AmbientQuotientRelativeSpace
public import FLT.Mazur.HilbertPolynomialSchemeParameterIdeal
public import FLT.Mazur.HilbertPolynomialParameterChart

/-!
# Full ambient containment on actual affine parameter tests

The kernel of the actual quotient ambient immersion restricts to the entire
extended original ideal. On Hilbert chart tests its containment in the actual
universal family is precisely the previously constructed relation criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (S : Type u) [CommRing S] [Algebra R S]
variable (a : Spec (.of S) ⟶ X)
variable (ha : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The quotient immersion restricts to all original equations on each affine base test. -/
theorem quotientRelativeImmersion_ker_affineTest :
    ((quotientRelativeImmersion R I K s).ker).comap
        (polynomialRelativeAffineChart R I s S a ha) =
      baseIdeal (.of (MvPolynomial I S)) (K.map (MvPolynomial.map (algebraMap R S))) := by
  rw [quotientRelativeImmersion_ker, ← Scheme.IdealSheafData.comap_comp,
    polynomialRelativeAffineChart_snd, baseIdeal_comap_specMap]
  rfl

/-- Equal actual affine parameters determine identical coordinate ideals. -/
theorem polynomialParameterIdeal_congr
    (f g : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hf : f ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (hg : g ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S))) (h : f = g) :
    polynomialParameterIdeal R I d S f hf = polynomialParameterIdeal R I d S g hg := by
  subst g
  rfl

variable (f : X ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d = s)
variable (w : Fin d → MvPolynomial I R) (b : ChartRing R I d w →ₐ[R] S)
variable (hb : a ≫ f = Spec.map (CommRingCat.ofHom b.toRingHom) ≫ polynomialHilbertChartι R I d w)

attribute [local irreducible] polynomialParameterIdeal pointIdeal

include hb

/-- An actual affine chart factorization recovers the full point ideal of the scheme family. -/
theorem polynomialSchemeParameterIdeal_chartTest :
    (polynomialSchemeParameterIdeal R I d s f hf).comap
        (polynomialRelativeAffineChart R I s S a ha) =
      baseIdeal (.of (MvPolynomial I S)) (pointIdeal R I d w b) := by
  rw [polynomialSchemeParameterIdeal_affineTest]
  have hg : (Spec.map (CommRingCat.ofHom b.toRingHom) ≫ polynomialHilbertChartι R I d w) ≫
      polynomialHilbertStructure R I d = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← hb, Category.assoc, hf, ha]
  exact congrArg (baseIdeal (.of (MvPolynomial I S)))
    ((polynomialParameterIdeal_congr R I d S _ _ _ hg hb).trans
      (polynomialParameterIdeal_chart R I d S w b hg))

/-- The chart test of actual quotient containment agrees with full polynomial ideal containment. -/
theorem ambientContainment_affineTest_iff :
    ((quotientRelativeImmersion R I K s).ker).comap
        (polynomialRelativeAffineChart R I s S a ha) ≤
      (polynomialSchemeParameterIdeal R I d s f hf).comap
        (polynomialRelativeAffineChart R I s S a ha) ↔
      K.map (MvPolynomial.map (algebraMap R S)) ≤ pointIdeal R I d w b := by
  rw [quotientRelativeImmersion_ker_affineTest,
    polynomialSchemeParameterIdeal_chartTest R I d s S a ha f hf w b hb, baseIdeal_le_iff]

end FLT.Mazur.HilbertChart

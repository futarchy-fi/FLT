/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricChartDatum
public import FLT.Mazur.AffineTensorCoactionRecognition

/-!
# Recognizing the actual geometric datum of a coefficient chart

The coaction determines an affine geometric datum. Consequently a fixed
reconstruction chart can be compatible with only one such datum, namely
the datum constructed from its canonical scalar-extension coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescentRecognition
open AffineGeometricDescent AffineGeometricOverlap AffinePullbackCoefficientRecognition
open AffineTensorCocycle AffineOverlapPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] toDatum tensorEquiv
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {M : (Spec S).Modules} [M.IsQuasicoherent]

/-- Evaluate the geometric coalgebra through the tensor datum. -/
theorem coalgebra_coaction_apply (D : Data φ M) (n : coefficients S M) :
    let := φ.hom.toAlgebra
    let := Module.compHom (coefficients S M) φ.hom
    let : IsScalarTower R S (coefficients S M) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    (coalgebra φ M D).a n =
      (toDatum R S M D.val D.property.1 D.property.2).coaction n := by
  dsimp only [coalgebra, toCoalgebra, ModuleCat.ofHom]
  rfl

/-- Equality of coactions determines the geometric datum. -/
theorem data_eq_of_coaction_eq (D E : Data φ M)
    (h : ∀ n : coefficients S M, (coalgebra φ M D).a n = (coalgebra φ M E).a n) :
    D = E := by
  let := φ.hom.toAlgebra
  let := Module.compHom (coefficients S M) φ.hom
  let : IsScalarTower R S (coefficients S M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  apply Subtype.ext
  apply tensorEquiv_injective R S M
  let DD := toDatum R S M D.val D.property.1 D.property.2
  let EE := toDatum R S M E.val E.property.1 E.property.2
  have hc : DD.coaction = EE.coaction := by
    apply LinearMap.ext
    intro n
    exact (coalgebra_coaction_apply φ D n).symm.trans
      ((h n).trans (coalgebra_coaction_apply φ E n))
  simpa only [DD, EE, toDatum_overlap] using DD.overlap_eq_of_coaction_eq (E := EE) hc

variable (A : (Spec R).Modules) [A.IsQuasicoherent]
variable (e : (pullback (Spec.map φ)).obj A ≅ M)

/-- One reconstruction chart determines at most one compatible geometric datum. -/
theorem compatible_data_unique (D E : Data φ M)
    (hD : CoactionCompatible φ A D e) (hE : CoactionCompatible φ A E e) : D = E := by
  apply data_eq_of_coaction_eq φ
  intro n
  have h := (cancel_epi (chart φ A e).hom).mp (hD.symm.trans hE)
  exact congrArg (fun f ↦ f n) h

/-- Compatibility is precisely equality with the chart's constructed geometric datum. -/
theorem coactionCompatible_iff_eq_chartData (D : Data φ M) :
    CoactionCompatible φ A D e ↔ D = chartData φ A e := by
  constructor
  · intro h
    exact compatible_data_unique φ A e D (chartData φ A e) h (chartData_compatible φ A e)
  · intro h
    subst D
    exact chartData_compatible φ A e

end FLT.Mazur.AffineGeometricDescentRecognition

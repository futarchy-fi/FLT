/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoefficientChartDatum
public import FLT.Mazur.AffineGeometricDescentRecognition

/-!
# Geometric descent data determined by a reconstruction chart

The coefficient chart of a reconstruction transports the canonical tensor
datum to an actual geometric datum. It satisfies coaction compatibility by
construction; comparison with a specified geometric datum remains an equality
of actual overlaps.
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
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable (A : (Spec R).Modules) [A.IsQuasicoherent]
variable {M : (Spec S).Modules} [M.IsQuasicoherent]
variable (e : (pullback (Spec.map φ)).obj A ≅ M)

/-- The geometric datum determined by the reconstruction's coefficient chart. -/
def chartData : Data φ M := by
  letI := φ.hom.toAlgebra
  letI := Module.compHom (coefficients S M) φ.hom
  letI : IsScalarTower R S (coefficients S M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let D := chartDatum φ (moduleSpecΓFunctor.obj A) (moduleSpecΓFunctor.obj M) (chart φ A e)
  exact ⟨fromDatum R S M D, fromDatum_diagonal R S M D, fromDatum_cocycle R S M D⟩

/-- Translating the chart's geometric datum returns its specified coefficient coalgebra. -/
theorem chartData_coaction :
    (coalgebra φ M (chartData φ A e)).a =
      (toCoalgebra φ (moduleSpecΓFunctor.obj M)
        (chartDatum φ (moduleSpecΓFunctor.obj A) (moduleSpecΓFunctor.obj M) (chart φ A e))).a := by
  let := φ.hom.toAlgebra
  let := Module.compHom (coefficients S M) φ.hom
  let : IsScalarTower R S (coefficients S M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  dsimp only [coalgebra, chartData]
  rw [toDatum_fromDatum]

/-- The reconstruction is compatible with its constructed geometric chart datum. -/
theorem chartData_compatible : CoactionCompatible φ A (chartData φ A e) e := by
  unfold CoactionCompatible
  rw [chartData_coaction]
  exact chartDatum_coaction φ (moduleSpecΓFunctor.obj A) (moduleSpecΓFunctor.obj M)
    (chart φ A e)

end FLT.Mazur.AffineGeometricDescentRecognition

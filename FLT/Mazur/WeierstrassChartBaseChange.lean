/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartCoefficientMap

/-!
# Base change of the actual normalized cubic algebras

The tensor product of a normalized chart with an arbitrary coefficient algebra
is the chart of the coefficient-extended Weierstrass equation. Both maps are
constructed from universal coordinates, without flatness assumptions.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j : Fin 3)

/-- A named tensor algebra keeps coefficient base-change proofs from unfolding its operations. -/
def ChartScalarExtension := S ⊗[R] Coordinate W j

instance chartScalarExtensionCommRing : CommRing (ChartScalarExtension S W j) :=
  inferInstanceAs (CommRing (S ⊗[R] Coordinate W j))

instance chartScalarExtensionAlgebra : Algebra R (ChartScalarExtension S W j) :=
  inferInstanceAs (Algebra R (S ⊗[R] Coordinate W j))

instance chartScalarExtensionAlgebraBase : Algebra S (ChartScalarExtension S W j) :=
  inferInstanceAs (Algebra S (S ⊗[R] Coordinate W j))

instance chartScalarExtensionTower : IsScalarTower R S (ChartScalarExtension S W j) :=
  inferInstanceAs (IsScalarTower R S (S ⊗[R] Coordinate W j))

/-- The tensor-to-chart map is the extension of the concrete coefficient map. -/
def chartBaseChangeForward :
    ChartScalarExtension S W j →ₐ[S] Coordinate (W.map (algebraMap R S)) j :=
  AlgHom.liftEquiv R S _ _ (chartCoefficientMap W j)

/-- Extension on a pure tensor multiplies its coefficient into the specialized chart. -/
@[simp] theorem chartBaseChangeForward_tmul (s : S) (a : Coordinate W j) :
    chartBaseChangeForward S W j (s ⊗ₜ[R] a) = s • chartCoefficientMap W j a := rfl

/-- The old universal coordinates solve the extended equation in the tensor product. -/
theorem chartBaseChange_equation :
    ((W.map (algebraMap R S)).map (algebraMap S (ChartScalarExtension S W j))).toProjective.Equation
      (fun i => (1 : S) ⊗ₜ[R] coord W j i) := by
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]
  exact projective_equation_of_hom (S := ChartScalarExtension S W j) W j
    Algebra.TensorProduct.includeRight

/-- Evaluation in the tensor product gives the inverse on the specialized chart. -/
def chartBaseChangeBackward :
    Coordinate (W.map (algebraMap R S)) j →ₐ[S] ChartScalarExtension S W j :=
  evaluation _ j (fun i => (1 : S) ⊗ₜ[R] coord W j i) (chartBaseChange_equation S W j)
    (by rw [coord_self, Algebra.TensorProduct.one_def])

/-- The inverse sends each specialized coordinate to the corresponding pure tensor. -/
@[simp] theorem chartBaseChangeBackward_coord (i : Fin 3) :
    chartBaseChangeBackward S W j (coord (W.map (algebraMap R S)) j i) =
      (1 : S) ⊗ₜ[R] coord W j i := evaluation_coord _ j _ _ _ i

/-- The tensor-to-chart map followed by evaluation fixes the specialized chart. -/
theorem chartBaseChangeForward_backward :
    (chartBaseChangeForward S W j).comp (chartBaseChangeBackward S W j) =
      AlgHom.id S (Coordinate (W.map (algebraMap R S)) j) := by
  apply hom_ext _ j
  intro i
  simp only [AlgHom.comp_apply, chartBaseChangeBackward_coord, chartBaseChangeForward_tmul,
    one_smul, chartCoefficientMap_coord, AlgHom.id_apply]

/-- Evaluation followed by the tensor-to-chart map fixes the whole tensor algebra. -/
theorem chartBaseChangeBackward_forward :
    (chartBaseChangeBackward S W j).comp (chartBaseChangeForward S W j) =
      AlgHom.id S (ChartScalarExtension S W j) := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext W j
  intro i
  change chartBaseChangeBackward S W j
    (chartBaseChangeForward S W j ((1 : S) ⊗ₜ[R] coord W j i)) = (1 : S) ⊗ₜ[R] coord W j i
  rw [chartBaseChangeForward_tmul, one_smul, chartCoefficientMap_coord,
    chartBaseChangeBackward_coord]

/-- Formation of a normalized cubic chart commutes with every coefficient extension. -/
def chartBaseChangeEquiv :
    ChartScalarExtension S W j ≃ₐ[S] Coordinate (W.map (algebraMap R S)) j :=
  AlgEquiv.ofAlgHom (chartBaseChangeForward S W j) (chartBaseChangeBackward S W j)
    (chartBaseChangeForward_backward S W j) (chartBaseChangeBackward_forward S W j)

/-- The comparison sends the original coordinates to those of the extended equation. -/
@[simp] theorem chartBaseChangeEquiv_coord (i : Fin 3) :
    chartBaseChangeEquiv S W j ((1 : S) ⊗ₜ[R] coord W j i) =
      coord (W.map (algebraMap R S)) j i := by
  change chartBaseChangeForward S W j ((1 : S) ⊗ₜ[R] coord W j i) = _
  rw [chartBaseChangeForward_tmul, one_smul, chartCoefficientMap_coord]

end FLT.Mazur.WeierstrassIntegralChart

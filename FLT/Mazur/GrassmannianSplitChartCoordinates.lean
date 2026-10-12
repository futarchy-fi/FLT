/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSplitQuotientChart

/-!
# Coordinates classify every point of a split Grassmannian chart

The selected summand supplies the quotient basis. In that basis the image of
the complementary summand is a unique matrix, and its normalized evaluation
recovers the entire original relation submodule.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {S : Type*} [CommRing S] {V : Type*} [AddCommGroup V] [Module S V] {d : ℕ}

/-- The selected summand gives the actual quotient basis of a chart point. -/
def splitChartBasisEquiv (N : SplitChart S V d) :
    (Fin d → S) ≃ₗ[S] (((Fin d → S) × V) ⧸ N.val.toSubmodule) :=
  LinearEquiv.ofBijective _ N.property

/-- Coordinates of the complementary summand in the actual quotient basis. -/
def splitChartCoordinates (N : SplitChart S V d) : V →ₗ[S] (Fin d → S) :=
  (splitChartBasisEquiv N).symm.toLinearMap.comp
    (N.val.toSubmodule.mkQ.comp (LinearMap.inr S (Fin d → S) V))

/-- Normalized evaluation recovers the entire quotient map in its selected basis. -/
theorem splitChartCoordinates_factor (N : SplitChart S V d) :
    (splitChartBasisEquiv N).toLinearMap.comp (splitChartEvaluation (splitChartCoordinates N)) =
      N.val.toSubmodule.mkQ := by
  apply LinearMap.ext
  intro x
  change splitChartBasisEquiv N
    (x.1 + (splitChartBasisEquiv N).symm (N.val.toSubmodule.mkQ (0, x.2))) = _
  rw [map_add, LinearEquiv.apply_symm_apply]
  change N.val.toSubmodule.mkQ (x.1, 0) + N.val.toSubmodule.mkQ (0, x.2) = _
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.eta]

/-- Reconstructing a point from its coordinates preserves its full relation submodule. -/
theorem splitChartCoordinates_kernel (N : SplitChart S V d) :
    (splitChartEvaluation (splitChartCoordinates N)).ker = N.val.toSubmodule := by
  rw [← LinearEquiv.ker_comp (splitChartBasisEquiv N), splitChartCoordinates_factor,
    Submodule.ker_mkQ]

/-- Every point of the chart comes from its constructed complementary coordinates. -/
theorem splitChartOfCoordinates_coordinates (N : SplitChart S V d) :
    splitChartOfCoordinates (splitChartCoordinates N) = N := by
  apply Subtype.ext
  apply Module.Grassmannian.ext
  exact splitChartCoordinates_kernel N

/-- A graph relation determines each complementary coordinate uniquely. -/
theorem splitChartOfCoordinates_injective :
    Function.Injective (splitChartOfCoordinates (S := S) (V := V) (d := d)) := by
  intro A B h
  have hk := congrArg (fun N : SplitChart S V d ↦ N.val.toSubmodule) h
  change (splitChartEvaluation A).ker = (splitChartEvaluation B).ker at hk
  ext y i
  have hy : (-A y, y) ∈ (splitChartEvaluation A).ker := by
    simp [splitChartEvaluation]
  rw [hk] at hy
  change -A y + B y = 0 at hy
  have he : B y = A y := eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using hy)
  exact congrFun he.symm i

/-- Recovering coordinates of a normalized quotient returns its original matrix. -/
theorem splitChartCoordinates_ofCoordinates (A : V →ₗ[S] (Fin d → S)) :
    splitChartCoordinates (splitChartOfCoordinates A) = A :=
  splitChartOfCoordinates_injective (splitChartOfCoordinates_coordinates _)

/-- Split Grassmannian charts are exactly spaces of complementary-coordinate matrices. -/
def splitChartCoordinateEquiv : (V →ₗ[S] (Fin d → S)) ≃ SplitChart S V d where
  toFun := splitChartOfCoordinates
  invFun := splitChartCoordinates
  left_inv := splitChartCoordinates_ofCoordinates
  right_inv := splitChartOfCoordinates_coordinates

end FLT.Mazur.GrassmannianChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCycles

/-!
# The bounded cycles quotient over the original base ring

The explicit quotient description remains linear after restriction of scalars.
These modules provide the concrete source for localization and tensor
base-change arguments on the bounded complex.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex FCurve

universe u v
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens)

variable {R : Type v} [Ring R] (ρ : R →+* Γ(X, ⊤))

/-- Every categorical differential with scalars restricted along the actual base map. -/
def baseDifferential (i j : ℕ) :
    let _ := fun k ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X k) ρ
    (complex U (moduleAbelianSheaf M)).X i →ₗ[R]
      (complex U (moduleAbelianSheaf M)).X j := by
  let _ := fun k ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X k) ρ
  exact
    { toFun := (complex U (moduleAbelianSheaf M)).d i j
      map_add' := map_add _
      map_smul' := fun r x ↦ complex_d_smul M U i j (ρ r) x }

/-- Cycles as a submodule over the chosen base ring. -/
def baseCycles (n : ℕ) :
    let _ := fun i ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X i) ρ
    Submodule R ((complex U (moduleAbelianSheaf M)).X n) := by
  let _ := fun i ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X i) ρ
  exact (baseDifferential M U ρ n ((ComplexShape.up ℕ).next n)).ker

/-- The base-ring linear incoming differential, valued in cycles. -/
def baseToCycles (n : ℕ) :
    let _termModule := fun i ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X i) ρ
    (complex U (moduleAbelianSheaf M)).X ((ComplexShape.up ℕ).prev n) →ₗ[R]
      baseCycles M U ρ n := by
  let _termModule := fun i ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X i) ρ
  exact
    { toFun := fun x ↦ ⟨(complex U (moduleAbelianSheaf M)).d _ n x,
        ((complex U (moduleAbelianSheaf M)).sc n).ab_zero_apply x⟩
      map_add' := fun x y ↦ Subtype.ext (map_add _ x y)
      map_smul' := fun r x ↦ Subtype.ext (complex_d_smul M U _ n (ρ r) x) }

/-- Boundaries as an actual base-ring submodule of cycles. -/
def baseBoundaries (n : ℕ) :
    Submodule R (baseCycles M U ρ n) := by
  let _termModule := fun i ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X i) ρ
  exact (baseToCycles M U ρ n).range

/-- Boundaries equal the incoming image restricted to the actual cycle submodule. -/
lemma baseBoundaries_eq_comap_range (n : ℕ) :
    let _ := fun i ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X i) ρ
    baseBoundaries M U ρ n =
      (baseDifferential M U ρ ((ComplexShape.up ℕ).prev n) n).range.comap
        (baseCycles M U ρ n).subtype := by
  let _ := fun i ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X i) ρ
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

/-- The quotient computation remains linear over an arbitrary base ring. -/
def baseHomologyQuotientEquiv (n : ℕ) :
    let _cohomologyModule := Module.compHom ((complex U (moduleAbelianSheaf M)).homology n) ρ
    ((complex U (moduleAbelianSheaf M)).homology n) ≃ₗ[R]
      (baseCycles M U ρ n ⧸ baseBoundaries M U ρ n) := by
  let _cohomologyModule := Module.compHom ((complex U (moduleAbelianSheaf M)).homology n) ρ
  exact
    { toAddEquiv := homologyQuotientAddEquiv M U n
      map_smul' := fun r x ↦ homologyQuotientAddEquiv_smul M U n (ρ r) x }

end FLT.Mazur.IncreasingCechScalars

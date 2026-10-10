/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FieldCoefficientCohomologyDimension
public import FLT.Mazur.IdealPowerExtensionCharts

/-!
# Proper field base change without auxiliary covers

Properness supplies separatedness and a finite affine cover. The dimension
comparison therefore applies directly to the actual pulled-back sheaf in every
degree, without passing a cover or a cohomology comparison as input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {k K : Type} [Field k] [Field K] {P X : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ Spec (CommRingCat.of K)}
  {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f]
  {g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]

include h

/-- Proper field base change preserves the dimensions of actual quasi-coherent cohomology. -/
theorem proper_field_cohomology_finrank (n : ℕ) :
    Module.finrank K (ModuleScalarH q ((pullback p).obj M) n) =
      Module.finrank k (ModuleScalarH f M n) := by
  let _ : IsNoetherian X := Chow.source_isNoetherian f
  let _ : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  obtain ⟨ι, hι, U, hU⟩ := IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)
  let _ : Finite ι := hι
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact IncreasingCechCoefficients.field_cohomology_finrank h M
    (fun i ↦ (U i).1) (fun i ↦ (U i).2) hU n

end FLT.Mazur.FCurve

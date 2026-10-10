/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertLocallySupported
public import FLT.Mazur.RelativeIdealFamilySupportOpen

/-!
# Classification from actual common affine neighborhoods of fibers

If every full finite fiber is contained in one original affine ambient chart,
its exact finite-family support opens form a base cover. This constructs
local support and hence the unique global classifying parameter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) (J : RelativeIdealFamilies z d s)
variable (hJ : ∀ x : X, ∃ i : A.Index, ∀ y : J.val.subscheme,
  (J.val.subschemeι ≫ pullback.fst s z) y = x →
    (J.val.subschemeι ≫ pullback.snd s z) y ∈ (A.chart i).opensRange)

/-- The exact support opens from common affine neighborhoods form an actual test-base cover. -/
def fiberSupportCover : X.OpenCover where
  I₀ := A.Index
  X i := (relativeIdealFamilySupportOpen z d s J (A.chart i).opensRange).toScheme
  f i := (relativeIdealFamilySupportOpen z d s J (A.chart i).opensRange).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    obtain ⟨i, hi⟩ := hJ x
    exact ⟨i, ⟨x, (mem_relativeIdealFamilySupportOpen z d s J _ x).mpr hi⟩, rfl⟩

omit [IsSeparated z] in
include hJ in
/-- A fiberwise common affine neighborhood produces actual local full-family support. -/
theorem locallySupportedFamily_of_fiberSupport : A.LocallySupportedFamily d s J := by
  let C := A.fiberSupportCover d s J hJ
  refine ⟨C, fun i ↦ i, fun i ↦ ?_⟩
  rw [relativeIdealAmbientHom_range]
  have h := (relativeIdealFamilySupportOpen_factorization z d s J (A.chart i).opensRange
    (C.f i ≫ s) (C.f i) rfl).mp (by
      change Set.range (relativeIdealFamilySupportOpen z d s J (A.chart i).opensRange).ι ⊆ _
      rw [Scheme.Opens.range_ι])
  rintro _ ⟨y, rfl⟩
  exact h ⟨y, rfl⟩

include hJ in
/-- Common affine neighborhoods of all full fibers give a unique actual global parameter. -/
theorem existsUnique_parameter_of_fiberSupport :
    ∃! p : A.GluedParameters d s, A.parameterFamily d s p = J := by
  have h := A.locallySupportedFamily_of_fiberSupport d s J hJ
  refine ⟨A.locallySupportedParameter d s J h,
    A.parameterFamily_locallySupportedParameter d s J h, fun p hp ↦ ?_⟩
  exact A.parameterFamily_injective d s
    (hp.trans (A.parameterFamily_locallySupportedParameter d s J h).symm)

end FLT.Mazur.HilbertChart.AmbientQuotientCharts

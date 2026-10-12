/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianDeterminantOpenUnits
public import FLT.Mazur.ModuleSheafUnitCocycle
public import FLT.Mazur.OpenSectionTopComparison

/-!
# The actual determinant cocycle in ambient sections

Transport the original determinant units through the canonical top-section
comparison. This retains their restriction laws and constructs a scalar cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
open Approximation FCurve.ModuleSheafUnitCocycle
universe u
set_option backward.isDefEq.respectTransparency false
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}
local notation "G" => ambientGrassmannianScheme R M ι d
local notation "chart" => ambientGrassmannianChart R M ι d

/-- The original determinant coordinate as an ambient regular function. -/
def determinantAmbientSection (i k : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) : Γ(G, U) :=
  U.topIso.hom (determinantOpenSection i k U hi)

/-- Ambient determinant coordinates restrict along the original inclusions. -/
theorem determinantAmbientSection_refine (i k : AmbientChartIndex R M ι d)
    (U V : (G).Opens) (h : V ≤ U) (hi : U ≤ (chart i).opensRange) :
    res h (determinantAmbientSection i k U hi) =
      determinantAmbientSection i k V (h.trans hi) := by
  unfold determinantAmbientSection
  rw [topIso_hom_restriction, determinantOpenSection_refine]

/-- The original common-chart determinant as a unit of ambient sections. -/
def determinantAmbientUnit (i j : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    Γ(G, U)ˣ := Units.map U.topIso.hom.hom.toMonoidHom (determinantOpenUnit i j U hi hj)

/-- The transported unit retains exactly the original determinant coordinate. -/
theorem determinantAmbientUnit_val (i j : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    (determinantAmbientUnit i j U hi hj : Γ(G, U)) =
      determinantAmbientSection i j U hi := by
  change U.topIso.hom (determinantOpenUnit i j U hi hj : Γ(U.toScheme, ⊤)) = _
  rw [determinantOpenUnit_val]
  rfl

/-- Every determinant coordinate obeys the original transition equation. -/
theorem determinantAmbientSection_transition (i j k : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    determinantAmbientSection i k U hi =
      (determinantAmbientUnit i j U hi hj : Γ(G, U)) *
        determinantAmbientSection j k U hj := by
  unfold determinantAmbientSection
  rw [determinantOpenSection_transition i j k U hi hj, map_mul]
  rfl

/-- Actual determinant units give a cocycle on all original chart opens. -/
def determinantCocycle : Cocycle (fun i : AmbientChartIndex R M ι d ↦ (chart i).opensRange)
    where
  unit := determinantAmbientUnit
  natural i j V W h hi hj := by
    rw [determinantAmbientUnit_val, determinantAmbientUnit_val,
      determinantAmbientSection_refine]
  refl i V h := by
    apply Units.ext
    rw [determinantAmbientUnit_val]
    change V.topIso.hom (determinantOpenSection i i V h) = 1
    rw [determinantOpenSection_self, map_one]
  cocycle i j k V hi hj hk := by
    apply Units.ext
    simp only [Units.val_mul, determinantAmbientUnit_val]
    exact (determinantAmbientSection_transition i j k V hi hj).symm

end FLT.Mazur.GrassmannianChart

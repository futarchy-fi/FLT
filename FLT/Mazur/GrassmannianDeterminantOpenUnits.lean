/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianDeterminantSchemeSections
public import FLT.Mazur.ModuleSheafOpenImageChart

/-!
# Determinant units on all common Grassmannian subopens

The actual chart coordinates construct units on every common subopen.
Their refinement law and multiplicative cocycle follow from the original
polynomial section identity, rather than an assumed line-bundle structure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
open Approximation ModuleSheafOpenImageChart
universe u
set_option backward.isDefEq.respectTransparency false
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}
local notation "G" => ambientGrassmannianScheme R M ι d
local notation "chart" => ambientGrassmannianChart R M ι d

/-- The original determinant evaluated on an arbitrary subopen of the first chart. -/
def determinantOpenSection (i k : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) : Γ(U.toScheme, ⊤) :=
  determinantTestSection i k (coordinate (chart i) U hi)

/-- The distinguished coordinate is one on every subopen of its chart. -/
@[simp] theorem determinantOpenSection_self (i : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) :
    determinantOpenSection i i U hi = 1 := determinantTestSection_self _ _

/-- Actual common-chart coordinates make the determinant invertible. -/
theorem determinantOpenSection_isUnit (i j : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    IsUnit (determinantOpenSection i j U hi) :=
  determinantTestSection_isUnit i j _ (coordinate (chart j) U hj)
    (by rw [coordinate_comp, coordinate_comp])

/-- The same determinant unit on the actual common open, independent of any point test. -/
def determinantOpenUnit (i j : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    Γ(U.toScheme, ⊤)ˣ := (determinantOpenSection_isUnit i j U hi hj).unit

/-- The unit retains the original selected determinant section. -/
theorem determinantOpenUnit_val (i j : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    (determinantOpenUnit i j U hi hj : Γ(U.toScheme, ⊤)) =
      determinantOpenSection i j U hi := (determinantOpenSection_isUnit i j U hi hj).unit_spec

/-- Every determinant section restricts along the original subopen inclusion. -/
theorem determinantOpenSection_refine (i k : AmbientChartIndex R M ι d)
    (U V : (G).Opens) (h : V ≤ U) (hi : U ≤ (chart i).opensRange) :
    ((G).homOfLE h).appTop (determinantOpenSection i k U hi) =
      determinantOpenSection i k V (h.trans hi) := by
  unfold determinantOpenSection determinantTestSection affineBaseSectionMap
  rw [← coordinate_refine (chart i) h hi, Scheme.Hom.comp_appTop]
  rfl

/-- The determinant units refine along the actual inclusion of every smaller open. -/
theorem determinantOpenUnit_refine (i j : AmbientChartIndex R M ι d)
    (U V : (G).Opens) (h : V ≤ U)
    (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    Units.map ((G).homOfLE h).appTop.hom.toMonoidHom (determinantOpenUnit i j U hi hj) =
      determinantOpenUnit i j V (h.trans hi) (h.trans hj) := by
  apply Units.ext
  change ((G).homOfLE h).appTop (determinantOpenUnit i j U hi hj : Γ(U.toScheme, ⊤)) = _
  rw [determinantOpenUnit_val, determinantOpenUnit_val, determinantOpenSection_refine]

/-- All determinant sections transform by the same unit on every common subopen. -/
theorem determinantOpenSection_transition (i j k : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange) :
    determinantOpenSection i k U hi =
      (determinantOpenUnit i j U hi hj : Γ(U.toScheme, ⊤)) *
        determinantOpenSection j k U hj := by
  rw [determinantOpenUnit_val]
  exact determinantTestSection_transition i j _ _
    (by rw [coordinate_comp, coordinate_comp]) k

/-- The original determinants satisfy the unit cocycle on every triple common subopen. -/
theorem determinantOpenUnit_cocycle (i j k : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) (hj : U ≤ (chart j).opensRange)
    (hk : U ≤ (chart k).opensRange) :
    determinantOpenUnit i k U hi hk =
      determinantOpenUnit i j U hi hj * determinantOpenUnit j k U hj hk := by
  apply Units.ext
  simp only [Units.val_mul, determinantOpenUnit_val]
  exact determinantTestSection_transition i j _ _
    (by rw [coordinate_comp, coordinate_comp]) k

end FLT.Mazur.GrassmannianChart

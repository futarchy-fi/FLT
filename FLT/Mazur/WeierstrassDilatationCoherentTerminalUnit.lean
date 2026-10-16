/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCoherentUnits
public import FLT.Mazur.WeierstrassDilatationArithmeticTerminalPolygon
public import FLT.Mazur.WeierstrassDilatationArithmeticSmoothingRestriction

/-!
# Compatible units for the original terminal smoothing

The primitive original constant coefficient supplies unit factors at every
order. Restriction from one order higher removes their choice ambiguity over
a domain and produces a compatible system for the full terminal charts.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages
variable {R : Type} [CommRing R] (π : R)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (u : Rˣ) (hu : b6 = π * ↑u)
local notation "c" => fun m ↦ arithmeticTerminalSmoothing π m W s b3 b4 b6 ha hs h2 h4 h6
local notation "v" => fun m ↦ arithmeticTerminalPolygonUnit π m W s b3 b4 b6
  ha hs h2 h3 h4 h6 u hu

/-- A terminal normalization factor obtained from the next arithmetic quotient. -/
def arithmeticCoherentTerminalUnit (m : ℕ) : (Quotient R π m)ˣ :=
  shiftedSmoothingUnit R π v m

/-- The constructed compatible factor retains the exact original smoothing. -/
theorem arithmeticCoherentTerminalUnit_spec (m : ℕ) :
    c m = parameter R π m *
      ↑(arithmeticCoherentTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m) :=
  shiftedSmoothingUnit_spec R π v c
    (fun m ↦ arithmeticTerminalSmoothing_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6)
    (fun m ↦ arithmeticTerminalPolygonUnit_spec π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 u hu) m

variable [IsDomain R] (hπ : π ≠ 0)
include hπ

/-- The actual selected terminal units agree across every adjacent quotient order. -/
theorem arithmeticCoherentTerminalUnit_restriction (m : ℕ) :
    Units.map (restriction R π m).toMonoidHom
      (arithmeticCoherentTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu (m + 1)) =
        arithmeticCoherentTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m :=
  shiftedSmoothingUnit_restriction R π v c
    (fun m ↦ arithmeticTerminalSmoothing_restriction R π m W s b3 b4 b6 ha hs h2 h4 h6)
    (fun m ↦ arithmeticTerminalPolygonUnit_spec π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 u hu) hπ m

/-- The scalar factors in the full coordinate formulas follow the original restriction. -/
theorem arithmeticCoherentTerminalUnit_coe_restriction (m : ℕ) :
    restriction R π m
      (arithmeticCoherentTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu (m + 1) :
        Quotient R π (m + 1)) =
      (arithmeticCoherentTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m :
        Quotient R π m) :=
  congrArg Units.val
    (arithmeticCoherentTerminalUnit_restriction π W s b3 b4 b6
      ha hs h2 h3 h4 h6 u hu hπ m)

end FLT.Mazur.WeierstrassDilatation

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoherentTerminalUnit
public import FLT.Mazur.WeierstrassRetainedStartOneQuotient

/-!
# Terminal normalization into the fixed depth-one target smoothing

The full terminal smoothing is normalized to the same inverse-tangent-square
multiple of the uniformizer used by the initial and retained nodes. The
ratio of the two constructed units is compatible at every arithmetic order.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages WeierstrassModificationX
variable {R : Type} [CommRing R] (π : R)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (u : Rˣ) (hu : b6 = π * ↑u)
local notation "v" => arithmeticCoherentTerminalUnit π W s b3 b4 b6
  ha hs h2 h3 h4 h6 u hu
local notation "q" => arithmeticStartOneQuotient W ha π
local notation "c" => fun m ↦ arithmeticTerminalSmoothing π m W s b3 b4 b6 ha hs h2 h4 h6
local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W ha (π ^ 1) π m

/-- The terminal scaling factor relative to the fixed normalized initial smoothing. -/
def arithmeticFixedTerminalUnit (m : ℕ) : (Quotient R π m)ˣ := v m * (q m)⁻¹

/-- The factor retains the whole terminal smoothing, including every higher-order term. -/
theorem arithmeticFixedTerminalUnit_spec (m : ℕ) :
    c m = τ m *
      ↑(arithmeticFixedTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m) := by
  calc
    c m = parameter R π m * ↑(v m) :=
      arithmeticCoherentTerminalUnit_spec π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m
    _ = (parameter R π m * ↑(q m)) *
        ↑(arithmeticFixedTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m) := by
      change parameter R π m * ↑(v m) =
        (parameter R π m * ↑(q m)) * (↑(v m) * (↑(q m)⁻¹ : Quotient R π m))
      rw [mul_mul_mul_comm, Units.mul_inv, mul_one]
    _ = _ := congrArg (fun t : Quotient R π m ↦ t *
      ↑(arithmeticFixedTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m))
        (arithmeticStartOneQuotient_relation W ha π m)

variable [IsDomain R] (hπ : π ≠ 0)
include hπ in
/-- The exact normalization ratio follows the original arithmetic quotient arrows. -/
theorem arithmeticFixedTerminalUnit_restriction (m : ℕ) :
    Units.map (restriction R π m).toMonoidHom
        (arithmeticFixedTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu (m + 1)) =
      arithmeticFixedTerminalUnit π W s b3 b4 b6 ha hs h2 h3 h4 h6 u hu m := by
  rw [arithmeticFixedTerminalUnit, map_mul, map_inv,
    arithmeticCoherentTerminalUnit_restriction π W s b3 b4 b6
      ha hs h2 h3 h4 h6 u hu hπ m,
    arithmeticStartOneQuotient_restriction]
  rfl

end FLT.Mazur.WeierstrassDilatation

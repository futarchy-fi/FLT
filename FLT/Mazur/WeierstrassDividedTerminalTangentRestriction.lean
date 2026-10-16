/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalWeightedReduction
public import FLT.Mazur.WeierstrassDividedClosedTerminalNormalization

/-!
# Original quotient naturality of the two terminal tangent scales

The arithmetic tangent coefficients and their scales follow the original
quotient maps and recover the existing full closed normalization weights.
No compatibility or existence of a higher-order node extension is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- The arithmetic scales are exactly the previous independent closed normalization scales. -/
theorem arithmeticTerminalTangentScale_closed (b : Bool) :
    arithmeticTerminalTangentScale data H 0 j hj u hu b =
      arithmeticClosedTerminalScale data H j hj u hu b := by
  unfold arithmeticTerminalTangentScale arithmeticClosedTerminalScale
  congr 1
  cases b
  · rfl
  · change -_ * _ = (-1) * _ * _
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one]
    ring

variable [IsDomain R] (hπ : π ≠ 0) (m : ℕ)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q" => restriction R π m
local notation "A₀" => zeroInitialTangentUnit (W.map (algebraMap R Q₀))
  (H.a1_unit.map (algebraMap R Q₀))
local notation "A₁" => zeroInitialTangentUnit (W.map (algebraMap R Q₁))
  (H.a1_unit.map (algebraMap R Q₁))

local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "V" => arithmeticFixedTerminalUnit π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu

include hπ in
/-- Both labeled tangent coefficients retain the actual arithmetic quotient arrow. -/
theorem arithmeticTerminalTangentCoefficient_restriction (b : Bool) :
    Units.map (q).toMonoidHom (arithmeticTerminalTangentCoefficient data H (m + 1) j hj u hu b) =
      arithmeticTerminalTangentCoefficient data H m j hj u hu b := by
  have hA : Units.map (q).toMonoidHom A₁ = A₀ := by
    apply Units.ext
    exact (q).commutes W.a₁
  cases b
  · exact hA
  · change Units.map (q).toMonoidHom (-((V (m + 1))⁻¹) * A₁) = -(V m)⁻¹ * A₀
    rw [map_mul, hA]
    congr 1
    have hv : Units.map (q).toMonoidHom (V (m + 1)) = V m :=
      arithmeticFixedTerminalUnit_restriction π W (π ^ (1 + j + 1))
        (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu hπ m
    have hm : Units.map (q).toMonoidHom (-((V (m + 1))⁻¹)) =
        -(Units.map (q).toMonoidHom (V (m + 1)))⁻¹ := by
      apply Units.ext
      exact (q).map_neg _
    exact hm.trans (congrArg (fun z : Q₀ˣ ↦ -z⁻¹) hv)

include hπ in
/-- The two constructed scale units commute with every consecutive original quotient. -/
theorem arithmeticTerminalTangentScale_restriction (b : Bool) :
    Units.map (q).toMonoidHom (arithmeticTerminalTangentScale data H (m + 1) j hj u hu b) =
      arithmeticTerminalTangentScale data H m j hj u hu b := by
  unfold arithmeticTerminalTangentScale
  rw [map_div, map_pow,
    arithmeticTerminalTangentCoefficient_restriction data H j hj u hu hπ m b]
  congr 2
  apply Units.ext
  exact (q).commutes W.a₁

end FLT.Mazur.WeierstrassDividedDepth

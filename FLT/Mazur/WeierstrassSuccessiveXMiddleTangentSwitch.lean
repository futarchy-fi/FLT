/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleConic

/-!
# Exchange the ordered tangent neighborhoods of the full middle fiber

The involution v ↦ -v-a₁ fixes both t and u. It preserves the entire
middle equation and exchanges its two ordered horizontal boundary lines.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "T" => coord W 0 0 0 0 c 0
local notation "V" => coord W 0 0 0 0 c 1
local notation "U" => coord W 0 0 0 0 c 2

/-- The original middle algebra has its actual tangent-switch endomorphism. -/
def middleTangentSwitch : A →ₐ[R] A :=
  evaluation W 0 0 0 0 c ![T, -V - algebraMap R A W.a₁, U]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h2, map_zero,
        zero_mul, zero_add, add_zero]
      linear_combination middle_conic_relation W c h2)
    (incidence W 0 0 0 0 c)

/-- The involution retains both incidence functions and the exact slope translation. -/
@[simp] theorem middleTangentSwitch_coord (i : Fin 3) :
    middleTangentSwitch W c h2 (coord W 0 0 0 0 c i) =
      ![T, -V - algebraMap R A W.a₁, U] i := evaluation_coord _ _ _ _ _ _ _ _ _ i

/-- Applying the actual tangent switch twice fixes every function of the full middle fiber. -/
theorem middleTangentSwitch_comp :
    (middleTangentSwitch W c h2).comp (middleTangentSwitch W c h2) = AlgHom.id R A := by
  apply hom_ext
  intro i
  fin_cases i <;> simp [middleTangentSwitch_coord]

/-- The full middle fiber, including u, is preserved by the tangent involution. -/
def middleTangentEquiv : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (middleTangentSwitch W c h2) (middleTangentSwitch W c h2)
    (middleTangentSwitch_comp W c h2) (middleTangentSwitch_comp W c h2)

/-- The first tangent denominator becomes minus the second tangent denominator. -/
@[simp] theorem middleTangentEquiv_first :
    middleTangentEquiv W c h2 (V + algebraMap R A W.a₁) = -V := by
  change middleTangentSwitch W c h2 (V + algebraMap R A W.a₁) = -V
  simp

/-- The actual involution preserves the original horizontal coordinate. -/
@[simp] theorem middleTangentEquiv_u : middleTangentEquiv W c h2 U = U :=
  middleTangentSwitch_coord W c h2 2

/-- The two ordered tangent opens cover the full middle fiber. -/
theorem middle_tangent_opens_cover (ha : IsUnit W.a₁) (p : PrimeSpectrum A) :
    V + algebraMap R A W.a₁ ∉ p.asIdeal ∨ -V ∉ p.asIdeal := by
  by_cases hv : -V ∈ p.asIdeal
  · left
    intro hd
    have h : algebraMap R A W.a₁ ∈ p.asIdeal := by
      have he : V + algebraMap R A W.a₁ + -V = algebraMap R A W.a₁ := by ring
      exact he ▸ p.asIdeal.add_mem hd hv
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (ha.map (algebraMap R A)))
  · exact Or.inr hv

end FLT.Mazur.WeierstrassSuccessiveX

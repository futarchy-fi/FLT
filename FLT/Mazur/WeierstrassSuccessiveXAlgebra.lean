/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart

/-!
# The x-direction chart of a successive divided modification

Keep the old horizontal coordinate u, the incidence coordinate t = π/u,
and the slope v. The equations are t*u = π and
v² + (a₁+c₃*t)*v = s*u+a₂+c₄*t+c₆*t². Keeping u is essential when the
previous divided cubic coefficient s is not a unit.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassSuccessiveX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The strict-transform equation with coordinates t, v, u in that order. -/
def equationPolynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + (C W.a₁ + C b3 * X 0) * X 1 -
    (C s * X 2 + C W.a₂ + C b4 * X 0 + C b6 * X 0 ^ 2)

/-- The divided cubic and incidence relation of the successive x-direction chart. -/
def relations : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {equationPolynomial W s b3 b4 b6, X 0 * X 2 - C π}

/-- The actual equation algebra, without any saturation assertion. -/
abbrev Coordinate := MvPolynomial (Fin 3) R ⧸ relations W s π b3 b4 b6

/-- The three universal chart coordinates. -/
def coord (i : Fin 3) : Coordinate W s π b3 b4 b6 := Ideal.Quotient.mk _ (X i)

/-- Evaluating at the universal coordinates is the defining quotient map. -/
theorem coord_aeval : aeval (coord W s π b3 b4 b6) =
    Ideal.Quotient.mkₐ R (relations W s π b3 b4 b6) := by
  ext i
  exact aeval_X _ i

/-- The universal successive x-direction coordinates satisfy the divided cubic. -/
theorem equation :
    coord W s π b3 b4 b6 1 ^ 2 +
        (algebraMap R _ W.a₁ + algebraMap R _ b3 * coord W s π b3 b4 b6 0) *
          coord W s π b3 b4 b6 1 =
      algebraMap R _ s * coord W s π b3 b4 b6 2 + algebraMap R _ W.a₂ +
        algebraMap R _ b4 * coord W s π b3 b4 b6 0 +
        algebraMap R _ b6 * coord W s π b3 b4 b6 0 ^ 2 := by
  have h : aeval (coord W s π b3 b4 b6) (equationPolynomial W s b3 b4 b6) = 0 := by
    rw [coord_aeval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
  simpa only [equationPolynomial, map_sub, map_add, map_mul, map_pow, map_one,
    aeval_C, aeval_X, sub_eq_zero] using h

/-- The incidence relation recovers the original scaling parameter. -/
theorem incidence : coord W s π b3 b4 b6 0 * coord W s π b3 b4 b6 2 =
    algebraMap R _ π := by
  have h : aeval (coord W s π b3 b4 b6) (X 0 * X 2 - C π) = 0 := by
    rw [coord_aeval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  simpa only [map_sub, map_mul, aeval_C, aeval_X, sub_eq_zero] using h

/-- Solutions of the two explicit relations give actual chart evaluations. -/
def evaluation {S : Type*} [CommRing S] [Algebra R S] (a : Fin 3 → S)
    (he : a 1 ^ 2 + (algebraMap R S W.a₁ + algebraMap R S b3 * a 0) * a 1 =
      algebraMap R S s * a 2 + algebraMap R S W.a₂ +
        algebraMap R S b4 * a 0 + algebraMap R S b6 * a 0 ^ 2)
    (hi : a 0 * a 2 = algebraMap R S π) : Coordinate W s π b3 b4 b6 →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval a) (by
    change relations W s π b3 b4 b6 ≤ RingHom.ker (aeval a).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · change aeval a (equationPolynomial W s b3 b4 b6) = 0
      simpa only [equationPolynomial, map_sub, map_add, map_mul, map_pow, map_one,
        aeval_C, aeval_X, sub_eq_zero] using he
    · have hf' := Set.mem_singleton_iff.mp hf
      subst f
      change aeval a (X 0 * X 2 - C π) = 0
      simpa only [map_sub, map_mul, aeval_X, aeval_C, sub_eq_zero] using hi)

/-- Evaluation preserves all three actual coordinates. -/
@[simp] theorem evaluation_coord {S : Type*} [CommRing S] [Algebra R S]
    (a : Fin 3 → S) (he hi) (i : Fin 3) :
    evaluation W s π b3 b4 b6 a he hi (coord W s π b3 b4 b6 i) = a i := aeval_X a i

/-- The three chart coordinates determine every algebra map. -/
@[ext] theorem hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (f g : Coordinate W s π b3 b4 b6 →ₐ[R] S)
    (h : ∀ i, f (coord W s π b3 b4 b6 i) = g (coord W s π b3 b4 b6 i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  exact MvPolynomial.algHom_ext h

end FLT.Mazur.WeierstrassSuccessiveX

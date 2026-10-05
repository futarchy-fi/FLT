/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentIdealPowerFiltration

/-!
# The actual ideal-adic coefficient quotients

The term at n is M / I^n M, using the image of the actual ideal action.
Canonical quotient maps give an inverse system of coherent sheaves with
epimorphic transitions. Degree zero is the zero quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility
open FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]

/-- The actual quotient by the n-th ideal-action image. -/
def quotient (n : ℕ) : X.Modules := cokernel (inclusion (I ^ n) M)

/-- The canonical projection from the original coefficient. -/
def projection (n : ℕ) : M ⟶ quotient I M n := cokernel.π (inclusion (I ^ n) M)

instance projection_epi (n : ℕ) : Epi (projection I M n) :=
  inferInstanceAs (Epi (cokernel.π _))

instance quotient_coherent (n : ℕ) : (quotient I M n).IsFinitePresentation :=
  coherent_cokernel (inclusion (I ^ n) M)

/-- The power-image sequence is short exact, including degree zero. -/
theorem quotient_shortExact (n : ℕ) :
    (ShortComplex.cokernelSequence (inclusion (I ^ n) M)).ShortExact :=
  (coherent_cokernelSequence (inclusion (I ^ n) M)).shortExact

/-- Reduction from a higher ideal-power quotient to a lower quotient. -/
def reduction {a b : ℕ} (h : a ≤ b) : quotient I M b ⟶ quotient I M a :=
  cokernel.desc (inclusion (I ^ b) M) (projection I M a) (by
    rw [← transition_comp I M h, Category.assoc]
    simp only [projection, cokernel.condition, comp_zero])

/-- Reduction is compatible with the quotient of the original coefficient. -/
@[reassoc (attr := simp)]
lemma projection_reduction {a b : ℕ} (h : a ≤ b) :
    projection I M b ≫ reduction I M h = projection I M a :=
  cokernel.π_desc _ _ _

instance reduction_epi {a b : ℕ} (h : a ≤ b) : Epi (reduction I M h) :=
  epi_of_epi_fac (projection_reduction I M h)

/-- Reduction at an equal index is the identity. -/
@[simp]
lemma reduction_refl (n : ℕ) : reduction I M (le_refl n) = 𝟙 _ := by
  apply (cancel_epi (projection I M n)).mp
  simp

/-- Reductions compose with their actual projection maps. -/
@[reassoc (attr := simp)]
lemma reduction_trans {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    reduction I M hbc ≫ reduction I M hab = reduction I M (hab.trans hbc) := by
  apply (cancel_epi (projection I M c)).mp
  simp

/-- The coefficient quotients form an actual inverse system. -/
def tower : ℕᵒᵖ ⥤ X.Modules where
  obj n := quotient I M n.unop
  map h := reduction I M (leOfHom h.unop)
  map_id n := reduction_refl I M n.unop
  map_comp f g := (reduction_trans I M (leOfHom g.unop) (leOfHom f.unop)).symm

/-- The initial quotient M / I^0 M is zero. -/
theorem quotient_zero_isZero : IsZero (quotient I M 0) := by
  have : IsIso (inclusion (I ^ 0) M) := by
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    infer_instance
  exact isZero_cokernel_of_epi _

end FLT.Mazur.IdealAdicQuotient

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Inertia fixes integral points of formally unramified algebras

Maps from a formally unramified algebra to a DVR are determined by reduction
modulo its maximal ideal. Consequently inertia fixes every such integral point.
This is a local algebra ingredient for the unramified point action of an étale model.
-/

@[expose] public section

open IsLocalRing

namespace Algebra.FormallyUnramified

/-- Reduction distinguishes maps from a formally unramified algebra to a DVR. -/
theorem algHom_ext_of_residue_eq
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsDomain B] [IsDiscreteValuationRing B]
    [FormallyUnramified R A] {f g : A →ₐ[R] B}
    (h : ∀ a, residue B (f a) = residue B (g a)) : f = g :=
  ext_of_iInf (maximalIdeal B)
    (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B) (maximalIdeal.isMaximal B).ne_top) h

/-- Inertia on a DVR fixes every point of a formally unramified algebra over the base. -/
theorem inertia_smul_algHom_apply
    {R A B G : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsDomain B] [IsDiscreteValuationRing B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G R B]
    [FormallyUnramified R A] (f : A →ₐ[R] B)
    (σ : G) (hσ : σ ∈ (maximalIdeal B).inertia G) (a : A) : σ • f a = f a := by
  have heq : (MulSemiringAction.toAlgHom R B σ).comp f = f := by
    apply algHom_ext_of_residue_eq
    intro x
    exact Ideal.Quotient.eq.mpr (Ideal.mem_inertia.mp hσ (f x))
  exact AlgHom.congr_fun heq a

end Algebra.FormallyUnramified

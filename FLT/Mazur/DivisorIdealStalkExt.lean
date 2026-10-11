/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierDivisorMultiplicity

/-!
# Recovering full divisor ideals from their stalks

Stalk comparisons determine the entire ideal sheaf, and commute with finite
products and powers. These statements retain nilpotents and multiplicities.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
universe u
variable {X : Scheme.{u}}

/-- Equality of all actual stalk ideals determines the full ideal sheaf. -/
theorem idealSheaf_eq_of_stalkIdeal_eq {I J : X.IdealSheafData}
    (h : ∀ x, stalkIdeal I x = stalkIdeal J x) : I = J := by
  apply Scheme.IdealSheafData.ext
  funext U
  apply U.2.ideal_ext_iff.mpr
  intro x hx
  simpa only [stalkIdeal_eq_map I x U hx, stalkIdeal_eq_map J x U hx] using h x

/-- The unit ideal has unit stalk at every point. -/
theorem stalkIdeal_one (x : X) : stalkIdeal (1 : X.IdealSheafData) x = 1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      TopologicalSpace.isOpen_univ
  rw [stalkIdeal_eq_map _ x ⟨U, hU⟩ hx]
  simp only [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.ideal_top,
    Pi.top_apply, Ideal.map_top, Ideal.one_eq_top]

/-- Powers of a full ideal commute with taking its actual stalk ideal. -/
theorem stalkIdeal_pow (I : X.IdealSheafData) (n : ℕ) (x : X) :
    stalkIdeal (I ^ n) x = stalkIdeal I x ^ n := by
  induction n with
  | zero => simp only [pow_zero, stalkIdeal_one]
  | succ n hn => rw [pow_succ, stalkIdeal_mul, hn, pow_succ]

/-- Finite products commute with taking actual stalk ideals. -/
theorem stalkIdeal_prod {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (x : X) :
    stalkIdeal (∏ i ∈ s, I i) x = ∏ i ∈ s, stalkIdeal (I i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, stalkIdeal_one]
  | @insert i s hi ih => simp only [Finset.prod_insert hi, stalkIdeal_mul, ih]

end FLT.Mazur.FCurve

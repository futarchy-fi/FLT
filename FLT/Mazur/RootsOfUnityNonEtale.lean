/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityScheme
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The nonetale prime-characteristic roots-of-unity subgroup

In characteristic p, the universal root minus one is a nonzero nilpotent in
the coordinate ring of mu_p. Over a field this proves that the constructed
finite locally free group scheme is not etale.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.RootsOfUnityNonEtale

open RootsOfUnityAlgebra RootsOfUnityScheme

variable (R : Type*) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime]

/-- The universal root differs from one as a coordinate-ring element. -/
theorem root_sub_one_ne_zero : (rootUnit R p).val - 1 ≠ 0 := by
  intro h
  have hc := congrArg (fun f : Coordinate R p ↦ f.coeff (1 : ZMod p)) (sub_eq_zero.mp h)
  simp [rootUnit, AddMonoidAlgebra.one_def] at hc

/-- In characteristic p the difference from the identity has vanishing pth power. -/
theorem root_sub_one_pow [CharP R p] : ((rootUnit R p).val - 1) ^ p = 0 := by
  let _ : CharP (Coordinate R p) p := charP_of_injective_algebraMap' R p
  have h := congrArg Units.val (rootUnit_pow R p)
  rw [sub_pow_char, one_pow]
  exact sub_eq_zero.mpr h

/-- This finite free algebra retains the infinitesimal structure of mu_p. -/
theorem not_isReduced [CharP R p] : ¬ IsReduced (Coordinate R p) := by
  intro h
  let _ := h
  exact root_sub_one_ne_zero R p (IsNilpotent.eq_zero ⟨p, root_sub_one_pow R p⟩)

/-- The actual subgroup over a characteristic-p field is not etale. -/
theorem not_etale (K : Type*) [Field K] [CharP K p] : ¬ Etale (model K p).hom := by
  intro h
  have he : (algebraMap K (Coordinate K p)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp h
  let _ := RingHom.etale_algebraMap.mp he
  exact not_isReduced K p (Algebra.FormallyUnramified.isReduced_of_field K (Coordinate K p))

end FLT.Mazur.RootsOfUnityNonEtale

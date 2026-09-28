/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HenselianComponents
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Connected Henselian algebras are local

For a Henselian pair with Artinian quotient, the primitive component idempotents
show that a nonzero connected algebra is local.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A nonzero Henselian algebra with Artinian special fibre and no nontrivial
idempotents is local. -/
theorem isLocalRing_of_henselian_idempotent_trivial
    {A : Type*} [CommRing A] [Nontrivial A] (I : Ideal A)
    [HenselianRing A I] [IsArtinianRing (A ⧸ I)]
    (hc : ∀ d : A, IsIdempotentElem d → d = 0 ∨ d = 1) : IsLocalRing A := by
  classical
  have hI : I ≠ ⊤ := by
    intro h
    have ht : (⊥ : Ideal A).jacobson = ⊤ := top_le_iff.mp (h ▸ HenselianRing.jac)
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp ht)
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hone (m : MaximalSpectrum (A ⧸ I)) : componentIdempotent I m = 1 := by
    let : Field ((A ⧸ I) ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    rcases hc _ (componentIdempotent_isIdempotent I m) with h | h
    · have hh := congrArg (fun x ↦ componentResidueMap I x m) h
      simp at hh
    · exact h
  have huniq (m n : MaximalSpectrum (A ⧸ I)) : m = n := by
    by_contra h
    let : Field ((A ⧸ I) ⧸ n.asIdeal) := Ideal.Quotient.field n.asIdeal
    have hh := congrArg (fun x ↦ componentResidueMap I x n) (hone m)
    simp [Pi.single_eq_of_ne (Ne.symm h)] at hh
  let : IsLocalRing (A ⧸ I) := IsLocalRing.of_unique_max_ideal (by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⧸ I)
    refine ⟨m, hm, fun n hn ↦ ?_⟩
    exact congrArg MaximalSpectrum.asIdeal (huniq ⟨n, hn⟩ ⟨m, hm⟩))
  let := isLocalHom_of_le_jacobson_bot I HenselianRing.jac
  exact (Ideal.Quotient.mk I).domain_isLocalRing

end ThreeAdicPlan

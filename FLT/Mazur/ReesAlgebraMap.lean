/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.ReesAlgebra

/-!
# Functorial maps of Rees algebras

A ring map carrying one ideal into another acts coefficientwise on their
Rees algebras. These maps retain the ordinary polynomial coordinates and
compose exactly, for later gluing along affine restrictions.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.Rees

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  (I : Ideal R) (J : Ideal S) (K : Ideal T)
  (f : R →+* S) (hf : I.map f ≤ J)

include hf in
/-- An ideal-preserving ring map carries each ideal power into the corresponding power. -/
lemma map_pow_le (n : ℕ) : (I ^ n).map f ≤ J ^ n := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' hf n

/-- The coefficientwise map on the actual Rees subalgebras. -/
def algebraMap : reesAlgebra I →+* reesAlgebra J :=
  ((Polynomial.mapRingHom f).comp (reesAlgebra I).val.toRingHom).codRestrict _ (by
    intro p n
    change (p.val.map f).coeff n ∈ J ^ n
    rw [Polynomial.coeff_map]
    exact map_pow_le I J f hf n (Ideal.mem_map_of_mem f (p.property n)))

/-- Coefficients are mapped by the original ring homomorphism. -/
lemma algebraMap_coeff (p : reesAlgebra I) (n : ℕ) :
    ((algebraMap I J f hf p : reesAlgebra J) : S[X]).coeff n = f (p.val.coeff n) :=
  Polynomial.coeff_map f n

/-- A homogeneous element retains its degree and its original coefficient map. -/
lemma algebraMap_monomial (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    algebraMap I J f hf ⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ =
      ⟨Polynomial.monomial n (f r), reesAlgebra.monomial_mem.mpr
        (map_pow_le I J f hf n (Ideal.mem_map_of_mem f hr))⟩ := by
  apply Subtype.ext
  exact Polynomial.map_monomial f

/-- Identity maps preserve the complete Rees algebra. -/
lemma algebraMap_id : algebraMap I I (RingHom.id R) (by simp) = RingHom.id _ := by
  ext p : 1
  apply Subtype.ext
  exact Polynomial.map_id

/-- Rees maps compose coefficientwise, independently of containment witnesses. -/
lemma algebraMap_comp (g : S →+* T) (hg : J.map g ≤ K) :
    (algebraMap J K g hg).comp (algebraMap I J f hf) =
      algebraMap I K (g.comp f) (by
        rw [← Ideal.map_map]
        exact (Ideal.map_mono hf).trans hg) := by
  ext p : 1
  apply Subtype.ext
  exact Polynomial.map_map f g p.val

end FLT.Mazur.Rees

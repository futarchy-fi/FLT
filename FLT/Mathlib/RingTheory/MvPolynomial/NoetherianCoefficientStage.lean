/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Adjoin.FG

/-! # Finite polynomial data over an arbitrary ring descends to a Noetherian stage -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R σ ι : Type*} [CommRing R]

/-- Finitely many polynomials have simultaneous coefficient lifts to one finitely
generated integer subalgebra. That subalgebra is Noetherian even when `R` is not. -/
theorem exists_noetherian_coefficient_stage [Finite ι] (f : ι → MvPolynomial σ R) :
    ∃ S : Subalgebra ℤ R, S.FG ∧ IsNoetherianRing S ∧
      ∃ g : ι → MvPolynomial σ S, ∀ i, map S.val.toRingHom (g i) = f i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let t := Finset.univ.biUnion (fun i ↦ (f i).coeffs)
  let S := Algebra.adjoin ℤ (t : Set R)
  have hS : S.FG := Subalgebra.fg_adjoin_finset t
  have hg (i : ι) : f i ∈ Set.range (map S.val.toRingHom) := by
    apply mem_range_map_iff_coeffs_subset.mpr
    intro r hr
    have hm : r ∈ S := Algebra.subset_adjoin
      (show r ∈ t from Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hr⟩)
    exact ⟨⟨r, hm⟩, rfl⟩
  choose g hg using hg
  exact ⟨S, hS, isNoetherianRing_of_fg hS, g, hg⟩

/-- Polynomial identities among the descended data hold exactly when their
reconstructions do. This includes all finite presentation identities encoded in the data. -/
theorem coefficient_stage_identity_iff (S : Subalgebra ℤ R)
    (f : ι → MvPolynomial σ R) (g : ι → MvPolynomial σ S)
    (hg : ∀ i, map S.val.toRingHom (g i) = f i) (F G : MvPolynomial ι ℤ) :
    aeval f F = aeval f G ↔ aeval g F = aeval g G := by
  let φ : MvPolynomial σ S →ₐ[ℤ] MvPolynomial σ R := mapAlgHom S.val
  have hφ : Function.Injective φ := map_injective _ Subtype.val_injective
  have hc : φ.comp (aeval g) = aeval f := by
    ext i : 1
    simpa [φ] using hg i
  have hm (H : MvPolynomial ι ℤ) : φ (aeval g H) = aeval f H := DFunLike.congr_fun hc H
  rw [← hm F, ← hm G]
  exact hφ.eq_iff

end MvPolynomial

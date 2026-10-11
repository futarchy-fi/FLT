/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResidueCoordinateDenominators
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Simultaneous monic polynomial lifts from residue fields

One principal-open coefficient ring lifts any finite family of monic residue
polynomials. The degrees and monicity are preserved, so the lifts can define
standard étale algebras after inverting their derivatives.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ResiduePolynomialLift
open Polynomial
variable {R K : Type} [CommRing R] [Field K]

/-- One principal open lifts a finite indexed family of residue values. -/
theorem exists_values (φ : R →+* K) (hφ : φ.SurjectiveOnStalks)
    {ι : Type} [Finite ι] (v : ι → K) :
    ∃ (r : R) (_ : φ r ≠ 0) (ψ : Localization.Away r →+* K),
      ψ.comp (algebraMap R (Localization.Away r)) = φ ∧
        ∃ a : ι → Localization.Away r, ∀ i, ψ (a i) = v i := by
  let _ := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  obtain ⟨r, hr, ψ, hψ, a, ha⟩ :=
    ResidueCoordinateDenominators.exists_localized_coordinates φ hφ (v ∘ e.symm)
  refine ⟨r, hr, ψ, hψ, a ∘ e, ?_⟩
  intro i
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using ha (e i)

/-- Lift finitely many monic polynomials together, with their degrees, over one principal open. -/
theorem exists_monic_family (φ : R →+* K) (hφ : φ.SurjectiveOnStalks)
    {ι : Type} [Finite ι] (p : ι → K[X]) (hp : ∀ i, (p i).Monic) :
    ∃ (r : R) (_ : φ r ≠ 0) (ψ : Localization.Away r →+* K),
      ψ.comp (algebraMap R (Localization.Away r)) = φ ∧
        ∃ q : ι → (Localization.Away r)[X], ∀ i,
          (q i).map ψ = p i ∧ (q i).natDegree = (p i).natDegree ∧ (q i).Monic := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨r, hr, ψ, hψ, a, ha⟩ := exists_values φ hφ
    (fun t : Σ i, (p i).support ↦ (p t.1).coeff t.2)
  have hlift (i : ι) : p i ∈ Polynomial.lifts ψ := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ (p i).support
    · exact ⟨a ⟨i, n, hn⟩, ha ⟨i, n, hn⟩⟩
    · exact ⟨0, (map_zero ψ).trans (notMem_support_iff.mp hn).symm⟩
  choose q hq using fun i ↦ lifts_and_natDegree_eq_and_monic (hlift i) (hp i)
  exact ⟨r, hr, ψ, hψ, q, hq⟩

end FLT.Mazur.ResiduePolynomialLift

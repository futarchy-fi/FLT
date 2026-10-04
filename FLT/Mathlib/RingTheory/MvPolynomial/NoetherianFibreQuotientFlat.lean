/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.NoetherianFibreCIFlat
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Polynomial.Basic

/-! # Noetherian polynomial quotients with fibrewise regular equations -/

@[expose] public noncomputable section

open scoped TensorProduct
open RingTheory.Sequence

namespace MvPolynomial

variable {R σ : Type*} [CommRing R] [IsNoetherianRing R] [Finite σ]

/-- Regularity of the original equations in every localized residue polynomial
fibre proves relative flatness of the original quotient. -/
theorem flat_quotient_of_residue_regular (rs : List (MvPolynomial σ R))
    (hrs : ∀ (p : Ideal R) [p.IsPrime] (Q : Ideal (MvPolynomial σ p.ResidueField)) [Q.IsPrime],
      Ideal.ofList (rs.map (map (algebraMap R p.ResidueField))) ≤ Q →
      IsWeaklyRegular (Localization.AtPrime Q)
        ((rs.map (map (algebraMap R p.ResidueField))).map
          (algebraMap _ (Localization.AtPrime Q)))) :
    Module.Flat R (MvPolynomial σ R ⧸ Ideal.ofList rs) := by
  apply Module.Flat.flat_quotient_of_fibre_regular
  intro p _ q _ hq
  let e := (algebraTensorAlgEquiv (σ := σ) R p.ResidueField).symm
  let Q := q.comap e
  have hQ : Ideal.ofList (rs.map (map (algebraMap R p.ResidueField))) ≤ Q := by
    apply Ideal.span_le.mpr
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    change e (map (algebraMap R p.ResidueField) b) ∈ q
    have hm : (Algebra.TensorProduct.includeRight : MvPolynomial σ R →ₐ[R]
        p.Fiber (MvPolynomial σ R)) b ∈ q :=
      hq (Ideal.subset_span (List.mem_map.mpr ⟨b, hb, rfl⟩))
    simpa [e] using hm
  have hr := hrs p Q hQ
  let e' := Localization.localAlgEquiv Q q e rfl
  have hr' := (e'.toRingEquiv.isWeaklyRegular_list_map _).mp hr
  have he : (((rs.map (map (algebraMap R p.ResidueField))).map
      (algebraMap _ (Localization.AtPrime Q))).map e'.toRingEquiv) =
      (rs.map (Algebra.TensorProduct.includeRight : MvPolynomial σ R →ₐ[R]
        p.Fiber (MvPolynomial σ R))).map (algebraMap _ (Localization.AtPrime q)) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a _
    change Localization.localRingHom Q q e.toRingHom rfl
      (algebraMap _ _ (map (algebraMap R p.ResidueField) a)) = _
    exact (Localization.localRingHom_to_map Q q e.toRingHom rfl
      (map (algebraMap R p.ResidueField) a)).trans (by simp [e])
  rw [he] at hr'
  exact hr'

end MvPolynomial

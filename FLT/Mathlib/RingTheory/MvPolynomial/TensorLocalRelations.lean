/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.BaseChangePresentation
public import FLT.Mathlib.RingTheory.Regular.LocalPresentationTransport

/-! # From coefficient fibre relations to the original tensor-product coordinates -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (k : Type*) [Field k] [Algebra R k] {d : ℕ}

/-- Local regular relations for the polynomial fibre give local regular relations
for its tensor-product presentation, retaining the whole kernel and equation count. -/
theorem exists_tensor_local_regular_relations
    (f : MvPolynomial (Fin d) R →ₐ[R] A)
    (h : ∀ (P : Ideal (MvPolynomial (Fin d) k)) [P.IsPrime],
      RingHom.ker (baseChangePresentation k f) ≤ P →
      ∃ rs : List (Localization.AtPrime P), rs.length = d ∧
        Ideal.ofList rs = (RingHom.ker (baseChangePresentation k f)).map (algebraMap _ _) ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime P) rs)
    (q : Ideal (k ⊗[R] MvPolynomial (Fin d) R)) [q.IsPrime]
    (hq : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R k) f) ≤ q) :
    ∃ rs : List (Localization.AtPrime q), rs.length = d ∧
      Ideal.ofList rs =
        (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R k) f)).map (algebraMap _ _) ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime q) rs := by
  let e := (algebraTensorAlgEquiv (σ := Fin d) R k).symm
  let g := baseChangePresentation k f
  have hk : RingHom.ker g =
      (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R k) f)).comap e.toRingHom := by
    ext s
    rfl
  have hkg : (RingHom.ker g).map e.toRingHom =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R k) f) := by
    rw [hk, Ideal.map_comap_of_surjective e.toRingHom e.surjective]
  have hP : RingHom.ker g ≤ q.comap e := by
    rw [hk]
    exact Ideal.comap_mono hq
  obtain ⟨rs, hlen, hgen, hreg⟩ := h (q.comap e) hP
  obtain ⟨ts, hlen', hgen', hreg'⟩ :=
    e.exists_local_regular_relations_of_equiv q (RingHom.ker g) rs hgen hreg
  exact ⟨ts, hlen'.trans hlen, hkg ▸ hgen', hreg'⟩

end MvPolynomial

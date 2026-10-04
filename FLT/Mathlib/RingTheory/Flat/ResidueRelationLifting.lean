/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.LocalizedRelationLifting
public import FLT.Mathlib.RingTheory.Flat.LocalizedResidueKernel

/-! # Lift actual residue-fibre relations to the original local presentation -/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]
  [Algebra.FinitePresentation R S] [Algebra.FinitePresentation R A] [Module.Flat R A]

/-- A relation family in the actual localized residue fibre lifts to a presentation
of the original target localization. Finite generation and the radical condition
are derived, with no Noetherian hypothesis on the base or source. -/
theorem exists_presentationAtPrime_of_residue_relations
    (f : S →ₐ[R] A) (hf : Function.Surjective f) (Q : Ideal A) [Q.IsPrime]
    (p : Ideal R) [p.IsPrime] (hp : p ≤ Q.comap (algebraMap R A))
    (q : Ideal (p.Fiber S)) [q.IsPrime]
    (hq : q.comap includeRight = Q.comap (f : S →+* A))
    {n : ℕ} (v : Fin n → Localization.AtPrime q)
    (hv : Ideal.span (Set.range v) =
      (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R p.ResidueField) f)).map
        (algebraMap (p.Fiber S) (Localization.AtPrime q))) :
    ∃ (w : Fin n → Localization.AtPrime (Q.comap (f : S →+* A)))
      (e : (Localization.AtPrime (Q.comap (f : S →+* A)) ⧸ Ideal.span (Set.range w)) ≃ₐ[R]
        Localization.AtPrime Q),
      (∀ i, Ideal.Quotient.mk _ (w i) =
        Ideal.Fiber.localizedQuotientEquivOfEq p q _ hq (v i)) ∧
      ∀ s, e (Ideal.Quotient.mk _ s) = f.presentationAtPrime Q s := by
  let e₀ := Ideal.Fiber.localizedQuotientEquivOfEq p q _ hq
  apply f.exists_presentationAtPrime_of_modBaseIdeal hf Q p hp (fun i ↦ e₀ (v i))
  rw [(f.presentationAtPrime Q).ker_modBaseIdeal (f.presentationAtPrime_surjective hf Q) p,
    f.ker_presentationAtPrime hf Q]
  have h := congrArg (Ideal.map e₀.toRingHom) hv
  rw [Ideal.map_span, ← Set.range_comp] at h
  exact h.trans (Ideal.Fiber.map_kernel_localizedQuotientEquivOfEq p q f hf _ hq)

end AlgHom

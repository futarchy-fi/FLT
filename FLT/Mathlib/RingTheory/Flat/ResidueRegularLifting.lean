/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.ResidueRelationLifting
public import FLT.Mathlib.RingTheory.Regular.LocalPresentationTransport
public import Mathlib.Data.List.OfFn

/-! # Retain the regular residue list while lifting the full local kernel -/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]
  [Algebra.FinitePresentation R S] [Algebra.FinitePresentation R A] [Module.Flat R A]

/-- Lift a regular residue list to generators of the original local kernel.
Regularity here is asserted on the residue quotient, not on the original base. -/
theorem exists_local_kernel_list_of_residue_regular
    (f : S →ₐ[R] A) (hf : Function.Surjective f) (Q : Ideal A) [Q.IsPrime]
    (p : Ideal R) [p.IsPrime] (hp : p ≤ Q.comap (algebraMap R A))
    (q : Ideal (p.Fiber S)) [q.IsPrime]
    (hq : q.comap includeRight = Q.comap (f : S →+* A))
    (rs : List (Localization.AtPrime q))
    (hgen : Ideal.ofList rs =
      (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R p.ResidueField) f)).map
        (algebraMap (p.Fiber S) (Localization.AtPrime q)))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime q) rs) :
    ∃ ws : List (Localization.AtPrime (Q.comap (f : S →+* A))),
      ws.length = rs.length ∧
      Ideal.ofList ws = (RingHom.ker f).map (algebraMap S _) ∧
      RingTheory.Sequence.IsRegular
        (Localization.AtPrime (Q.comap (f : S →+* A)) ⧸
          p.map (algebraMap R (Localization.AtPrime (Q.comap (f : S →+* A)))))
        (ws.map (Ideal.Quotient.mk
          (p.map (algebraMap R (Localization.AtPrime (Q.comap (f : S →+* A))))))) := by
  have hs : Ideal.span (Set.range rs.get) = Ideal.ofList rs := by
    congr 1
    ext x
    simp
  obtain ⟨w, e, hw, he⟩ := f.exists_presentationAtPrime_of_residue_relations hf Q p hp q hq
    rs.get (hs.trans hgen)
  have hk : Ideal.span (Set.range w) = RingHom.ker (f.presentationAtPrime Q) := by
    ext s
    change s ∈ Ideal.span (Set.range w) ↔ f.presentationAtPrime Q s = 0
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← he, map_eq_zero_iff e e.injective]
  refine ⟨List.ofFn w, List.length_ofFn, ?_, ?_⟩
  · rw [← f.ker_presentationAtPrime hf Q, ← hk]
    exact congrArg Ideal.span (Set.ext fun x ↦ List.mem_ofFn' w x)
  · let e₀ := Ideal.Fiber.localizedQuotientEquivOfEq p q _ hq
    have hr := (e₀.toRingEquiv.isRegular_list_map rs).mp hreg
    have hlist : (List.ofFn w).map (Ideal.Quotient.mk _) = rs.map e₀ := by
      calc
        _ = List.ofFn (fun i ↦ e₀ (rs.get i)) := by
          rw [List.map_ofFn]
          exact congrArg List.ofFn (funext hw)
        _ = rs.map e₀ := by
          simpa only [List.map_ofFn, Function.comp_def] using
            congrArg (List.map e₀) (List.ofFn_get rs)
    rw [hlist]
    exact hr

end AlgHom

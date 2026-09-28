/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalHopfPresentation
public import FLT.Mathlib.RingTheory.LocalizedPresentation

/-! # Minimal local presentations of finite local Hopf algebras -/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open MvPolynomial

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
  [IsLocalRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [PerfectRing k p]

include p

omit [CharP A p] in
/-- A finite local commutative Hopf algebra has a quotient presentation by
exactly its cotangent dimension many relations in the polynomial source
localized at the augmentation maximal ideal. -/
theorem exists_minimal_local_quotient_presentation :
    ∃ P : Algebra.Generators k A
        (Fin (Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent)),
      (∀ i, Bialgebra.counitAlgHom k A (P.val i) = 0) ∧
      let f := aeval (R := k) P.val
      ∃ r : Fin (Module.finrank k
          (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent) → f.localizedSource,
        Nonempty ((f.localizedSource ⧸ Ideal.span (Set.range r)) ≃ₐ[k] A) := by
  obtain ⟨P, hx, r, hr⟩ := exists_minimal_square_presentation (k := k) (A := A) p
  let f := aeval (R := k) P.val
  let rL (i) : f.localizedSource := algebraMap P.Ring f.localizedSource (r i)
  have hker : RingHom.ker f.localizeAtMaximal = Ideal.span (Set.range rL) :=
    f.ker_localizeAtMaximal_eq_span r hr
  refine ⟨P, hx, rL, ⟨?_⟩⟩
  exact (Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f.localizeAtMaximal_surjective P.aeval_val_surjective))

end HopfAlgebra

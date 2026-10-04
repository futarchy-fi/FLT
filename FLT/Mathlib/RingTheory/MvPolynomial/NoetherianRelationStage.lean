/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.NoetherianCoefficientStage
public import FLT.Mathlib.RingTheory.MvPolynomial.RelationBaseChange

/-! # Reconstruct a relation quotient from a Noetherian coefficient stage -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {R σ ι : Type*} [CommRing R] [Finite ι]

/-- Every finite relation quotient over an arbitrary ring is the exact base change
of a quotient over a finitely generated integer subalgebra. Polynomial representatives
and relations are retained; no regularity or flatness is asserted at the stage. -/
theorem exists_noetherian_relation_stage (f : ι → MvPolynomial σ R) :
    ∃ S : Subalgebra ℤ R, S.FG ∧ IsNoetherianRing S ∧
      ∃ (g : ι → MvPolynomial σ S) (_hg : ∀ i, map S.val.toRingHom (g i) = f i),
        ∃ e : (R ⊗[S] (MvPolynomial σ S ⧸ Ideal.span (Set.range g))) ≃ₐ[R]
            (MvPolynomial σ R ⧸ Ideal.span (Set.range f)),
          ∀ q : MvPolynomial σ S, e (1 ⊗ₜ[S] Ideal.Quotient.mk _ q) =
            Ideal.Quotient.mk _ (map S.val.toRingHom q) := by
  obtain ⟨S, hS, hN, g, hg⟩ := exists_noetherian_coefficient_stage f
  have he : Ideal.span (Set.range fun i ↦ map (algebraMap S R) (g i)) =
      Ideal.span (Set.range f) := by
    congr 1
    exact congrArg Set.range (funext hg)
  let e := (relationBaseChangeEquiv (S := R) g).trans (Ideal.quotientEquivAlgOfEq R he)
  refine ⟨S, hS, hN, g, hg, e, fun q ↦ ?_⟩
  change Ideal.quotientEquivAlgOfEq R he
    (relationBaseChangeEquiv g (1 ⊗ₜ[S] Ideal.Quotient.mk _ q)) = _
  rw [relationBaseChangeEquiv_one_tmul_mk]
  rfl

end MvPolynomial

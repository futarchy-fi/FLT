/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.NoetherianCoefficientStage
public import FLT.Mathlib.RingTheory.MvPolynomial.PrincipalRelationBaseChange

/-! # Noetherian coefficient stages retain the principal denominator -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {R σ ι : Type*} [CommRing R] [Finite ι]

/-- Descend both the relations and the denominator, and reconstruct the actual principal
quotient chart after base change. Its map is specified on every polynomial representative. -/
theorem exists_noetherian_principal_stage (f : ι → MvPolynomial σ R)
    (a : MvPolynomial σ R) :
    ∃ S : Subalgebra ℤ R, S.FG ∧ IsNoetherianRing S ∧
      ∃ (g : ι → MvPolynomial σ S) (b : MvPolynomial σ S),
        (∀ i, map S.val.toRingHom (g i) = f i) ∧ map S.val.toRingHom b = a ∧
        ∃ e : (R ⊗[S] Localization.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range g)) b)) ≃ₐ[R]
          Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a),
          ∀ q : MvPolynomial σ S,
            e (1 ⊗ₜ[S] algebraMap _ _ (Ideal.Quotient.mk (Ideal.span (Set.range g)) q)) =
              algebraMap _ _ (Ideal.Quotient.mk (Ideal.span (Set.range f))
                (map S.val.toRingHom q)) := by
  obtain ⟨S, hS, hN, data, hd⟩ :=
    exists_noetherian_coefficient_stage (Option.elim' a f)
  let g := fun i ↦ data (some i)
  let b := data none
  have hg (i : ι) : map S.val.toRingHom (g i) = f i := hd (some i)
  have hb : map S.val.toRingHom b = a := hd none
  have hI : Ideal.span (Set.range fun i ↦ map (algebraMap S R) (g i)) =
      Ideal.span (Set.range f) := congrArg Ideal.span (congrArg Set.range (funext hg))
  let e := (relationBaseChangeEquiv (S := R) g).trans (Ideal.quotientEquivAlgOfEq R hI)
  have he (q : MvPolynomial σ S) : e (1 ⊗ₜ[S] Ideal.Quotient.mk _ q) =
      Ideal.Quotient.mk _ (map S.val.toRingHom q) := by
    change Ideal.quotientEquivAlgOfEq R hI
      (relationBaseChangeEquiv g (1 ⊗ₜ[S] Ideal.Quotient.mk _ q)) = _
    rw [relationBaseChangeEquiv_one_tmul_mk]
    rfl
  let E := IsLocalization.Away.baseChangeEquiv e (Ideal.Quotient.mk _ b)
    (Ideal.Quotient.mk _ a) (by rw [he, hb])
  refine ⟨S, hS, hN, g, b, hg, hb, E, fun q ↦ ?_⟩
  change IsLocalization.Away.baseChangeEquiv e _ _ _ _ = _
  rw [IsLocalization.Away.baseChangeEquiv_tmul, he]

end MvPolynomial

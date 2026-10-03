/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudModelUpperBound

/-!
# Generic filtrations with rank-one scalar factors

Each step is an actual exact generic sequence. The quotient carries a finite
field action of rank one commuting with Galois. No integral scalar action,
coordinate presentation, or rigidity is part of the filtration data.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- A finite generic filtration whose quotient factors are finite-field lines. -/
def FF.HasScalarFiltration (p : ℕ) (X : FF R K) : ℕ → Prop
  | 0 => Nat.card X.Points = 1
  | n + 1 => ∃ (S Q : FF R K) (i : GenericGaloisHom S X) (q : GenericGaloisHom X Q),
      Function.Injective i ∧ Function.Surjective q ∧
      (∀ x, q x = 0 ↔ ∃ s, i s = x) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F Q.Points)
        (_ : SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) Q.Points),
        Module.finrank F Q.Points = 1 ∧ S.HasScalarFiltration p n

/-- A prescribed generic isomorphism transports the filtration without changing its factors. -/
theorem FF.HasScalarFiltration.of_generic_bijective {p n : ℕ} {X Y : FF R K}
    (hX : X.HasScalarFiltration p n) (e : GenericGaloisHom X Y)
    (he : Function.Bijective e) : Y.HasScalarFiltration p n := by
  cases n with
  | zero => exact (Nat.card_congr (Equiv.ofBijective e he).symm).trans hX
  | succ n =>
    obtain ⟨S, Q, i, q, hi, hq, hex, hF⟩ := hX
    let inv := e.inverse he
    have hleft (x : X.Points) : inv (e x) = x := GenericGaloisHom.inverse_apply e he x
    have hright (y : Y.Points) : e (inv y) = y :=
      (AddEquiv.ofBijective e.toAddMonoidHom he).apply_symm_apply y
    refine ⟨S, Q, e.comp i, q.comp inv, he.injective.comp hi, ?_, ?_, hF⟩
    · intro z
      obtain ⟨x, hx⟩ := hq z
      exact ⟨e x, by change q (inv (e x)) = z; rw [hleft, hx]⟩
    · intro y
      change q (inv y) = 0 ↔ ∃ s, e (i s) = y
      rw [hex]
      constructor
      · rintro ⟨s, hs⟩
        exact ⟨s, (congrArg e hs).trans (hright y)⟩
      · rintro ⟨s, hs⟩
        exact ⟨s, he.injective (hs.trans (hright y).symm)⟩

end ThreeAdicPlan

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantGroupPoints
public import FLT.GroupScheme.RaynaudHenselianScalarRigidity

/-!
# The scalar filtration of a constant group of prime order

Cardinality constructs the prime-field line and its one-step scalar filtration.
This allows Henselian rigidity over general DVRs, including finite extensions
which have not been identified with a number-field completion.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false

variable (R K H : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field K] [PerfectField K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup H] [Finite H] (p : ℕ) [Fact p.Prime]

/-- A constant prime-order model has the explicit scalar filtration of length one. -/
theorem constantGroupModel_prime_scalarFiltration (hc : Nat.card H = p) :
    (constantGroupModel R K H).HasScalarFiltration p 1 := by
  let X := constantGroupModel R K H
  let S := constantGroupModel R K PUnit
  have hcard : Nat.card X.Points = p := (constantGroupPoint_card R K H).trans hc
  have hkill : ∀ x : X.Points, p • x = 0 := by
    intro x
    rw [← hcard]
    let := Fintype.ofFinite X.Points
    rw [← Fintype.card_eq_nat_card]
    exact card_nsmul_eq_zero
  let : Module (ZMod p) X.Points := AddCommGroup.zmodModule hkill
  let : SMulCommClass (ZMod p) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points :=
    ⟨fun r g x => by
      rw [constantGroupModel_smul, constantGroupModel_smul]⟩
  have hdim : Module.finrank (ZMod p) X.Points = 1 := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    change p ^ Module.finrank (ZMod p) X.Points = p ^ 1
    let := Fintype.ofFinite X.Points
    have hm := Module.card_eq_pow_finrank (K := ZMod p) (V := X.Points)
    rw [Fintype.card_eq_nat_card, hcard, ZMod.card] at hm
    simpa only [pow_one] using hm.symm
  let : Subsingleton S.Points :=
    (constantGroupPointEquiv R K PUnit).symm.injective.subsingleton
  refine ⟨S, X, 0, DistribMulActionHom.id _,
    fun _ _ _ => Subsingleton.elim _ _, Function.surjective_id, ?_,
    ZMod p, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hdim, ?_⟩
  · intro x
    change x = 0 ↔ ∃ _ : S.Points, (0 : X.Points) = x
    simp only [exists_const, eq_comm]
  · change Nat.card S.Points = 1
    rw [constantGroupPoint_card]
    exact Nat.card_unique

end ThreeAdicPlan

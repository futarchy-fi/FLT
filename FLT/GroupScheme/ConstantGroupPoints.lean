/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantGroupModel

/-!
# All points of the integral constant model

Integral evaluation separates the finite group elements. Coordinate rank
proves that these are all geometric points, giving the specified additive
comparison and the trivial Galois action on the full point group.
-/

@[expose] public noncomputable section
open HopfAlgebra.CartierDual
namespace ThreeAdicPlan

variable (R K A : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup A] [Finite A]

/-- Distinct elements give distinct integral evaluation points. -/
theorem constantGroupPoint_injective : Function.Injective (constantGroupPoint R K A) := by
  classical
  intro a b h
  have he := congrArg (constantGroupModel R K A).integralPoints h
  rw [constantGroupPoint_integral, constantGroupPoint_integral] at he
  let φ := (constantGroupCoordinates R K A).symm (Pi.single (Multiplicative.ofAdd a) 1)
  have hv := AlgHom.congr_fun he φ
  have hinj : Function.Injective (algebraMap R (AlgebraicClosure K)) :=
    (algebraMap K _).injective.comp (IsFractionRing.injective R K)
  have hv := hinj hv
  change constantGroupCoordinates R K A φ (Multiplicative.ofAdd a) =
    constantGroupCoordinates R K A φ (Multiplicative.ofAdd b) at hv
  simp only [φ, AlgEquiv.apply_symm_apply, Pi.single_apply] at hv
  by_contra hab
  simp [Ne.symm hab] at hv

variable [IsLocalRing R] [PerfectField K]

omit [IsDomain R] [IsFractionRing R K] in
/-- The constant model has exactly the cardinality of the prescribed group. -/
theorem constantGroupPoint_card : Nat.card (constantGroupModel R K A).Points = Nat.card A := by
  let := Fintype.ofFinite A
  rw [← FF.coordinate_finrank]
  rw [(constantGroupCoordinates R K A).toLinearEquiv.finrank_eq]
  simp only [Module.finrank_pi, Fintype.card_eq_nat_card, Nat.card_congr Multiplicative.toAdd]

/-- The constructed evaluation points exhaust the geometric generic fibre. -/
theorem constantGroupPoint_bijective : Function.Bijective (constantGroupPoint R K A) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨constantGroupPoint_injective R K A, (constantGroupPoint_card R K A).symm⟩

/-- The original finite group is additively identified with all points of its model. -/
def constantGroupPointEquiv : A ≃+ (constantGroupModel R K A).Points :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (constantGroupPoint R K A) (constantGroupPoint_add R K A))
    (constantGroupPoint_bijective R K A)

/-- Every geometric point of the constant model is Galois fixed. -/
theorem constantGroupModel_smul (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : (constantGroupModel R K A).Points) : g • x = x := by
  obtain ⟨a, rfl⟩ := constantGroupPoint_bijective R K A |>.2 x
  exact constantGroupPoint_fixed R K A a g

end ThreeAdicPlan

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.CharacterBasis
public import FLT.GaloisRepresentation.Extensions.LiftCocycle

/-!
# Changes of coordinates for cocycles obtained from lifts

This links coefficient transport to the actual difference construction of
E04. Rescaling a sub-line basis by a and a quotient lift by b multiplies
the resulting coefficient cocycle by b/a.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G A B V : Type*} [Group G] [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]
    [DistribMulAction G V] (i : A →+ V) (v : V)
    (hv : ∀ g : G, g • v - v ∈ i.range) (e : A ≃+ B)

include hv in
/-- Coefficient changes preserve the quotient-invariance range condition. -/
theorem lift_range_change_coefficients (g : G) :
    g • v - v ∈ (i.comp e.symm.toAddMonoidHom).range := by
  refine ⟨e (liftCocycle i v hv g), ?_⟩
  simpa using liftCocycle_spec i v hv g

/-- The cocycle of the same lift in new coefficient coordinates is its transport by e. -/
theorem liftCocycle_change_coefficients (hi : Function.Injective i) :
    liftCocycle (i.comp e.symm.toAddMonoidHom) v (lift_range_change_coefficients i v hv e) =
      fun g ↦ e (liftCocycle i v hv g) := by
  symm
  apply liftCocycle_unique (i.comp e.symm.toAddMonoidHom)
    (fun x y h ↦ e.symm.injective (hi h))
  intro g
  simpa using liftCocycle_spec i v hv g

section Lines

variable {k : Type*} [Field k] [Module k V] [SMulCommClass G k V]
    (j : k →ₗ[k] V) (hj : Function.Injective j) (w : V)
    (hw : ∀ g : G, g • w - w ∈ j.toAddMonoidHom.range)
    (a b : kˣ)

/-- The injection in coordinates after changing the sub-line basis by a. -/
def lineBasisInjection : k →ₗ[k] V := (a : k) • j

include hj in
/-- The changed injection is still injective. -/
theorem lineBasisInjection_injective : Function.Injective (lineBasisInjection j a) := by
  intro x y h
  apply hj
  have h' := congrArg (fun z : V ↦ (a : k)⁻¹ • z) h
  simpa only [lineBasisInjection, LinearMap.smul_apply, smul_smul,
    inv_mul_cancel₀ a.ne_zero, one_smul] using h'

include hw in
/-- Rescaling the quotient lift preserves invariance modulo the changed sub-line. -/
theorem lift_range_change_bases (g : G) :
    g • ((b : k) • w) - (b : k) • w ∈ (lineBasisInjection j a).toAddMonoidHom.range := by
  refine ⟨((b / a : kˣ) : k) * liftCocycle j.toAddMonoidHom w hw g, ?_⟩
  change (a : k) • j (((b / a : kˣ) : k) • liftCocycle j.toAddMonoidHom w hw g) = _
  have heq : j (liftCocycle j.toAddMonoidHom w hw g) = g • w - w :=
    liftCocycle_spec j.toAddMonoidHom w hw g
  rw [map_smul, smul_smul, Units.val_div_eq_div_val, mul_div_cancel₀ _ a.ne_zero,
    heq, smul_sub, smul_comm g (b : k) w]

include hj in
/-- Changing the two line bases multiplies the actual lifted cocycle by b/a. -/
theorem liftCocycle_change_bases :
    liftCocycle (lineBasisInjection j a).toAddMonoidHom ((b : k) • w)
      (lift_range_change_bases j w hw a b) =
        fun g ↦ ((b / a : kˣ) : k) * liftCocycle j.toAddMonoidHom w hw g := by
  symm
  apply liftCocycle_unique _ (lineBasisInjection_injective j hj a)
  intro g
  change (a : k) • j (((b / a : kˣ) : k) • liftCocycle j.toAddMonoidHom w hw g) = _
  have heq : j (liftCocycle j.toAddMonoidHom w hw g) = g • w - w :=
    liftCocycle_spec j.toAddMonoidHom w hw g
  rw [map_smul, smul_smul, Units.val_div_eq_div_val, mul_div_cancel₀ _ a.ne_zero,
    heq, smul_sub, smul_comm g (b : k) w]

end Lines

end GaloisRepresentation.Extensions

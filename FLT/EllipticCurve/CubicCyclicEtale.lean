/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInvariantTrace
public import FLT.EllipticCurve.CubicCyclicDedekind

/-! # Prime cyclic parameters over noetherian integral coefficient bases

The scalar action is free on all field-valued coordinate points. The
trace retraction therefore makes the invariant inclusion universally
injective under base change and its algebra flat. Étale field fibers
then establish finite étaleness of the actual scalar quotient over the
whole base, without a Dedekind hypothesis or invertibility of p-1.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]

/-- Scalar units give distinct coordinate characters at every field-valued point. -/
theorem nonzeroTorsionCoordinate_action_injective
    (K : Type u) [Field K] (f : NonzeroTorsionRing W p →+* K) :
    Function.Injective (fun a : (ZMod p)ˣ =>
      fun b : NonzeroTorsionRing W p => f (a • b)) := by
  let : Algebra R K := (f.comp (algebraMap R (NonzeroTorsionRing W p))).toAlgebra
  let φ : NonzeroTorsionRing W p →ₐ[R] K := { f with commutes' := fun _ => rfl }
  intro a b hab
  have he : φ.comp (nonzeroTorsionRingScalar W p a).toAlgHom =
      φ.comp (nonzeroTorsionRingScalar W p b).toAlgHom :=
    AlgHom.ext (fun x => congrFun hab x)
  have hp := congrArg (nonzeroTorsionCoordinatePointEquiv W p K) he
  rw [nonzeroTorsionCoordinatePoint_scalar, nonzeroTorsionCoordinatePoint_scalar] at hp
  apply inv_injective
  apply scalarOrbitPoint_injective W p K (nonzeroTorsionCoordinatePointEquiv W p K φ)
  dsimp only
  rw [map_inv, map_inv]
  exact hp

/-- Prime-level scalar invariants are flat over any noetherian integral coefficient base. -/
theorem scalarInvariantRing_flat :
    Module.Flat R (TorsionScalarInvariantRing W p) := by
  have := nonzeroTorsionRing_etale W p
  exact freeInvariant_flat R (NonzeroTorsionRing W p) (ZMod p)ˣ
    (nonzeroTorsionCoordinate_action_injective W p)

/-- The prime scalar invariant inclusion stays injective under arbitrary base change. -/
theorem scalarInvariantTensor_injective_prime
    (S : Type u) [CommRing S] [Algebra R S] :
    Function.Injective (Algebra.TensorProduct.lTensor S (TorsionScalarInvariantRing W p).val :
      S ⊗[R] TorsionScalarInvariantRing W p →ₐ[S] S ⊗[R] NonzeroTorsionRing W p) :=
  freeInvariantTensor_injective R (NonzeroTorsionRing W p) (ZMod p)ˣ S
    (nonzeroTorsionCoordinate_action_injective W p)

/-- Every field fiber of the prime scalar invariant algebra is étale. -/
theorem scalarInvariantRing_fieldFiber_etale
    (K : Type u) [Field K] [Algebra R K] :
    Algebra.Etale K (K ⊗[R] TorsionScalarInvariantRing W p) := by
  have := nonzeroTorsionRing_etale W p
  have := torsionScalarInvariantRing_finite W p
  exact finiteAlgebra_etale_of_injective_field K _ _
    (Algebra.TensorProduct.lTensor K (TorsionScalarInvariantRing W p).val)
    (scalarInvariantTensor_injective_prime W p K)

/-- The prime scalar invariant algebra is étale over the whole integral coefficient base. -/
theorem scalarInvariantRing_etale :
    Algebra.Etale R (TorsionScalarInvariantRing W p) := by
  have := torsionScalarInvariantRing_finite W p
  have := scalarInvariantRing_flat W p
  exact finiteFlat_etale_of_fieldFibers R _ (scalarInvariantRing_fieldFiber_etale W p)

/-- The actual prime cyclic parameter scheme is étale over the coefficient base. -/
theorem scalarQuotientModel_etale : Etale (scalarQuotientModel W p).hom := by
  change Etale (Spec.map (CommRingCat.ofHom
    (algebraMap R (TorsionScalarInvariantRing W p))))
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact (RingHom.etale_algebraMap).mpr (scalarInvariantRing_etale W p)

/-- The actual prime-level generator-forgetting map is étale over the whole base. -/
theorem scalarQuotientMap_etale : Etale (scalarQuotientMap W p).left := by
  have := scalarQuotientModel_etale W p
  have : Etale ((scalarQuotientMap W p).left ≫ (scalarQuotientModel W p).hom) := by
    rw [(scalarQuotientMap W p).w]
    exact nonzeroTorsionModel_etale W p Fact.out
  exact Etale.of_comp (scalarQuotientMap W p).left (scalarQuotientModel W p).hom

/-- Every field fiber of the prime scalar invariant algebra has dimension p+1. -/
theorem scalarInvariantRing_field_finrank
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] TorsionScalarInvariantRing W p) = p + 1 := by
  have := scalarInvariantRing_fieldFiber_etale W p K
  let Ω := AlgebraicClosure K
  calc
    Module.finrank K (K ⊗[R] TorsionScalarInvariantRing W p) =
        Nat.card ((K ⊗[R] TorsionScalarInvariantRing W p) →ₐ[K] Ω) :=
      GaloisModule.finrank_eq_natCard_algHom K Ω _
    _ = Nat.card (TorsionScalarInvariantRing W p →ₐ[R] Ω) :=
      Nat.card_congr (AlgHom.liftEquiv R K (TorsionScalarInvariantRing W p) Ω).symm
    _ = Nat.card (pointSource (R := R) Ω ⟶ scalarQuotientModel W p) :=
      Nat.card_congr (scalarQuotientCoordinatePointEquiv W p)
    _ = p + 1 := scalarQuotientFieldPoints_card W p Ω

end WeierstrassCurve.CubicCharts

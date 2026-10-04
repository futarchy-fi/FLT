/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalConnectedComponents

/-! # The identity component of an original rational-place model -/

@[expose] public noncomputable section
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.FF
attribute [local instance] rationalFiniteFlat_henselian rationalSpecialFiber_artinian
variable {p : ℕ} [Fact p.Prime]
  (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- The integral counit singles out exactly one connected component. -/
theorem existsUnique_rationalIdentityComponent : ∃! m : X.RationalComponentIndex,
    Coalgebra.counit (R := O) (X.rationalComponentIdempotent m) = 1 := by
  classical
  let : Fintype X.RationalComponentIndex := Fintype.ofFinite _
  let ε := Bialgebra.counitAlgHom O X.CoordinateRing
  have hc := (componentIdempotent_complete (rationalSpecialIdeal p X.CoordinateRing)).map
    ε.toRingHom
  have hex : ∃ m : X.RationalComponentIndex, ε (X.rationalComponentIdempotent m) = 1 := by
    by_contra h
    push Not at h
    have hz (m : X.RationalComponentIndex) : ε (X.rationalComponentIdempotent m) = 0 :=
      (IsIdempotentElem.iff_eq_zero_or_one.mp (hc.idem m)).resolve_right (h m)
    have hs := hc.complete
    change ∑ m, ε (X.rationalComponentIdempotent m) = 1 at hs
    simp only [hz, Finset.sum_const_zero] at hs
    exact zero_ne_one hs
  obtain ⟨m, hm⟩ := hex
  refine ⟨m, hm, fun n hn ↦ ?_⟩
  by_contra hnm
  have hh := hc.ortho hnm
  change ε (X.rationalComponentIdempotent n) * ε (X.rationalComponentIdempotent m) = 0 at hh
  rw [show ε (X.rationalComponentIdempotent n) = 1 from hn, hm, one_mul] at hh
  exact one_ne_zero hh

/-- The component containing the identity section of the group scheme. -/
def rationalIdentityComponentIndex : X.RationalComponentIndex :=
  X.existsUnique_rationalIdentityComponent.choose

/-- The identity-component idempotent has counit one. -/
@[simp] theorem counit_rationalIdentityComponentIdempotent :
    Coalgebra.counit (R := O) (X.rationalComponentIdempotent
      X.rationalIdentityComponentIndex) = 1 :=
  X.existsUnique_rationalIdentityComponent.choose_spec.1

/-- The identity section factors through the connected component selected by the counit. -/
def rationalIdentityComponentCounit : X.RationalComponentAlgebra
  X.rationalIdentityComponentIndex →ₐ[O] O :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom O X.CoordinateRing) (by
    change Ideal.span {1 - X.rationalComponentIdempotent X.rationalIdentityComponentIndex} ≤
      RingHom.ker (Bialgebra.counitAlgHom O X.CoordinateRing).toRingHom
    apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    change (Bialgebra.counitAlgHom O X.CoordinateRing)
      (1 - X.rationalComponentIdempotent X.rationalIdentityComponentIndex) = 0
    rw [map_sub, map_one, Bialgebra.counitAlgHom_apply,
      X.counit_rationalIdentityComponentIdempotent, sub_self])
end ThreeAdicPlan.FF

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantRationalTateBasis
public import FLT.GroupScheme.PDivisibleTateRootDuality
public import FLT.GroupScheme.PDivisibleTateRank

/-! # The actual cyclotomic root module is finite free of rank one -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime] (hp : 2 < p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- Evaluation against the actual constant generator identifies its dual Tate module with roots. -/
def rationalPlaceCyclotomicTateRootEquiv :
    (ConstantRationalPower.system p hp).CartierTate ≃ₗ[ℤ_[p]]
      TateRootModule (AlgebraicClosure K) p :=
  ((ConstantRationalPower.system p hp).tateRootDuality.trans
    (LinearEquiv.arrowCongr (ConstantRationalPower.constantTateEquiv p hp).symm
      (LinearEquiv.refl ℤ_[p] _))).trans (LinearMap.ringLmapEquivSelf ℤ_[p] ℤ_[p] _)

/-- The identification uses the original Cartier pairing with the original constant generator. -/
theorem rationalPlaceCyclotomicTateRootEquiv_value
    (y : (ConstantRationalPower.system p hp).CartierTate) (n : ℕ) :
    tateRootValue (AlgebraicClosure K) p n (tateRootEval (AlgebraicClosure K) p n
      (rationalPlaceCyclotomicTateRootEquiv p hp y)) =
        Additive.ofMul ((ConstantRationalPower.system p hp).cartierTatePairing y
          (ConstantRationalPower.generator p hp) n) := by
  change tateRootValue (AlgebraicClosure K) p n (tateRootEval (AlgebraicClosure K) p n
    ((ConstantRationalPower.system p hp).tateRootDuality y
      (ConstantRationalPower.constantTateEquiv p hp 1))) = _
  rw [ConstantRationalPower.constantTateEquiv_one]
  rfl

include hp

/-- The root module is finite over Z_p, proved from the actual height-one dual system. -/
theorem rationalPlace_tateRoot_finite :
    Module.Finite ℤ_[p] (TateRootModule (AlgebraicClosure K) p) := by
  let : Module.Finite ℤ_[p] (ConstantRationalPower.system p hp).CartierTate :=
    (ConstantRationalPower.system p hp).cartierDual.tateSequences_finite
  exact Module.Finite.equiv (rationalPlaceCyclotomicTateRootEquiv p hp)

/-- The actual coherent-root module is free over Z_p. -/
theorem rationalPlace_tateRoot_free :
    Module.Free ℤ_[p] (TateRootModule (AlgebraicClosure K) p) := by
  let : Module.Free ℤ_[p] (ConstantRationalPower.system p hp).CartierTate :=
    (ConstantRationalPower.system p hp).cartierDual.tateSequences_free
  exact Module.Free.of_equiv (rationalPlaceCyclotomicTateRootEquiv p hp)

/-- The actual coherent-root line has rank one, independently of a chosen primitive generator. -/
theorem rationalPlace_tateRoot_finrank :
    Module.finrank ℤ_[p] (TateRootModule (AlgebraicClosure K) p) = 1 := by
  rw [← (rationalPlaceCyclotomicTateRootEquiv p hp).finrank_eq]
  exact (ConstantRationalPower.system p hp).cartierDual.tateSequences_finrank
end ThreeAdicPlan

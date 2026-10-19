/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluCoefficientOverlapCover

/-!
# Effective descent from the original cubic coefficient cover

The proved kernel-pair compatibility descends any Galois-invariant morphism
to a relatively separated target. The result retains the original cover,
its original geometric map, and its specified base map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] [CharZero K]
  (E : WeierstrassCurve K) {Y Z : Scheme} (i : Y ⟶ Z) [IsSeparated i]
  (j : integralCurve E ⟶ Z)

local notation "c" => integralCoefficientMorphism (S := L) E
local notation "EL" => E.map (algebraMap K L)

variable (f : integralCurve (E.map (algebraMap K L)) ⟶ Y)
  (hb : f ≫ i = integralCoefficientMorphism (S := L) E ≫ j)
  (h : ∀ a : L ≃ₐ[K] L, integralGaloisMap E a ≫ f = f)

include hb h in
/-- Invariance gives compatibility for all pairs coequalized by the original cover. -/
theorem coefficientInvariant_compatible {T : Scheme}
    (a b : T ⟶ integralCurve EL) (he : a ≫ c = b ≫ c) : a ≫ f = b ≫ f := by
  have H := congrArg (fun k ↦ pullback.lift a b he ≫ k)
    (coefficientInvariant_kernelPair E i j f hb h)
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using H

/-- The descended map on the original cubic, constructed by effective epimorphism descent. -/
def coefficientInvariantDesc : integralCurve E ⟶ Y :=
  EffectiveEpi.desc c f (coefficientInvariant_compatible E i j f hb h)

/-- Pulling back the constructed map recovers the entire original geometric morphism. -/
@[reassoc] theorem coefficientInvariantDesc_fac :
    c ≫ coefficientInvariantDesc E i j f hb h = f := EffectiveEpi.fac ..

/-- Descent retains the specified original base morphism. -/
@[reassoc] theorem coefficientInvariantDesc_base :
    coefficientInvariantDesc E i j f hb h ≫ i = j := by
  apply (cancel_epi c).mp
  rw [coefficientInvariantDesc_fac_assoc, hb]

/-- No second morphism on the original cubic can have the same geometric pullback. -/
theorem coefficientInvariantDesc_unique (m : integralCurve E ⟶ Y) (hm : c ≫ m = f) :
    m = coefficientInvariantDesc E i j f hb h := by
  apply (cancel_epi c).mp
  rw [coefficientInvariantDesc_fac, hm]

end WeierstrassCurve.Velu

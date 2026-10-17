/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticMobiusParameterAlgebra
public import FLT.Mazur.WeierstrassModificationXInitialMobiusLaurentCoefficient
public import FLT.Mazur.WeierstrassModificationXArithmeticRestrictionMaps

/-!
# Original quotient squares for the complete Mobius parameter

The curve, all divided coefficients and the exact normalized smoothing
are transported through the original arithmetic restriction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages PolygonScalingNaturality WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
universe u

/-- Transport the complete parameter across specified equalities of all original coefficients. -/
theorem initialMobiusLaurentEquiv_coefficient_of_eq
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    {W : WeierstrassCurve R} {W' : WeierstrassCurve S}
    {s τ b3 b4 b6 : R} {s' τ' b3' b4' b6' : S}
    {I : Ideal R} {J : Ideal S} {hI : IsNilpotent I} {hJ : IsNilpotent J}
    (hf : I ≤ J.comap f) {ha : IsUnit W.a₁} {ha' : IsUnit W'.a₁}
    {hτ : s = W.a₁ ^ 2 * τ} {hτ' : s' = W'.a₁ ^ 2 * τ'}
    {hs : s ∈ I} {h2 : W.a₂ ∈ I} {h3 : b3 ∈ I} {h4 : b4 ∈ I} {h6 : b6 ∈ I}
    {hs' : s' ∈ J} {h2' : W'.a₂ ∈ J} {h3' : b3' ∈ J} {h4' : b4' ∈ J}
    {h6' : b6' ∈ J}
    (hW : W.map f = W') (hS : f s = s') (ht : f τ = τ')
    (h3c : f b3 = b3') (h4c : f b4 = b4') (h6c : f b6 = b6') :
    (coeffMap f).comp
        (initialMobiusLaurentEquiv W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6).toRingHom =
      (initialMobiusLaurentEquiv W' ha' s' τ' hτ' b3' b4' b6' J hJ
        hs' h2' h3' h4' h6').toRingHom.comp (coeffMap f) := by
  subst W' s' b3' b4' b6'
  exact initialMobiusLaurentEquiv_coefficient f W ha s τ hτ τ' hτ' ht
    b3 b4 b6 I J hf hI hJ hs h2 h3 h4 h6

variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "E" => fun k ↦ arithmeticInitialMobiusEquiv π k W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "f" => AlgHom.toRingHom (restriction R π m)

/-- The full arithmetic Mobius parameter respects the exact coefficient quotient. -/
theorem arithmeticInitialMobiusEquiv_restriction :
    (coeffMap f).comp (E (m + 1)).toRingHom =
      (E m).toRingHom.comp (coeffMap f) := by
  unfold arithmeticInitialMobiusEquiv
  exact initialMobiusLaurentEquiv_coefficient_of_eq
    (arithmeticParameterIdeal_restriction R π m)
    (arithmeticInitialCurve_restriction R π m W)
    ((restriction R π m).commutes s)
    (arithmeticInitialMobiusSmoothing_restriction W ha s π m)
    ((restriction R π m).commutes b3) ((restriction R π m).commutes b4)
    ((restriction R π m).commutes b6)

end FLT.Mazur.WeierstrassModificationX

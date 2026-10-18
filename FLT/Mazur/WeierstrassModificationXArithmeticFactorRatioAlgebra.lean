/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioLaurent
public import FLT.Mazur.PolygonSmoothingPunctureSpecCalculus

/-!
# The full arithmetic squared-factor substitution on Laurent algebras

Keep the unreduced automorphism, its original coefficient square, and its
reciprocal residue. These are the algebra inputs to the concrete cyclic seed.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages PolygonSmoothing PolygonScalingNaturality LaurentPolynomial
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "K" => Ideal.map (algebraMap Q Q[T;T⁻¹]) J

/-- The entire squared-factor equivalence, with every nilpotent coefficient retained. -/
def arithmeticFactorRatioLaurentEquiv : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  factorRatioLaurentEquiv (W.map q) (ha.map q) (q s) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (arithmeticCoefficient_mem π m hs)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
    (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)

local notation "E" => fun k ↦
  arithmeticFactorRatioLaurentEquiv π k W s b3 b4 b6 ha hs h2 h3 h4 h6

/-- Its spectrum is exactly the previously constructed full boundary parameter. -/
theorem arithmeticFactorRatioLaurentEquiv_spec : punctureSpecIso (E m) =
    arithmeticFactorRatioLaurentIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6 := rfl

/-- The full substitution differs from inversion only in the arithmetic coefficient ideal. -/
theorem arithmeticFactorRatioLaurentEquiv_sub_mem (z : Q[T;T⁻¹]) :
    E m z - invert z ∈ K := by
  apply LaurentNilpotentReparametrization.hom_sub_mem K (E m).toAlgHom invert.toAlgHom
  change E m (T 1) - invert (T 1) ∈ K
  dsimp only [arithmeticFactorRatioLaurentEquiv]
  rw [factorRatioLaurentEquiv_T, invert_T]
  exact factorRatioLaurentUnit_sub_mem (W.map q) (ha.map q) (q s) (q b3) (q b4)
    (q b6) J (arithmeticParameterIdeal_nilpotent π m) (arithmeticCoefficient_mem π m hs)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
    (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)

/-- The exact arithmetic order-zero substitution is inversion. -/
theorem arithmeticFactorRatioLaurentEquiv_zero : E 0 = invert := by
  ext z : 1
  have hz := arithmeticFactorRatioLaurentEquiv_sub_mem π 0 W s b3 b4 b6
    ha hs h2 h3 h4 h6 z
  have hp : parameter R π 0 = 0 := by
    simpa only [Nat.zero_add, pow_one] using parameter_pow R π 0
  simpa only [hp, ideal, Ideal.span_singleton_zero, Ideal.map_bot,
    Submodule.mem_bot, sub_eq_zero] using hz

/-- The complete algebra parameter keeps the original arithmetic quotient square. -/
theorem arithmeticFactorRatioLaurentEquiv_restriction :
    (coeffMap (restriction R π m).toRingHom).comp (E (m + 1)).toRingHom =
      (E m).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  have h := arithmeticFactorRatioLaurentIso_restriction π m W s b3 b4 b6
    ha hs h2 h3 h4 h6
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ at h
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end FLT.Mazur.WeierstrassModificationX

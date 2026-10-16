/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFactorRatioLaurentNaturality
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialFactorRatio
public import FLT.Mazur.WeierstrassModificationXArithmeticPunctureRestriction

/-!
# The exact corrected Laurent parameter at every arithmetic order

The constructed automorphism preserves the whole original node boundary and
commutes with consecutive quotient restrictions, including its inverse.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
universe u

/-- The corrected Laurent square allows independently named target coefficients. -/
@[reassoc] theorem factorRatioLaurentIso_coefficient_of_eq
    {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    {W : WeierstrassCurve A} {U : WeierstrassCurve B}
    {s b3 b4 b6 : A} {s' b3' b4' b6' : B}
    {I : Ideal A} {J : Ideal B} {hI : IsNilpotent I} {hJ : IsNilpotent J}
    (hf : I ≤ J.comap f) {ha : IsUnit W.a₁} {ha' : IsUnit U.a₁}
    {hs : s ∈ I} {h2 : W.a₂ ∈ I} {h3 : b3 ∈ I} {h4 : b4 ∈ I} {h6 : b6 ∈ I}
    {hs' : s' ∈ J} {h2' : U.a₂ ∈ J} {h3' : b3' ∈ J} {h4' : b4' ∈ J} {h6' : b6' ∈ J}
    (hW : W.map f = U) (hS : f s = s')
    (hB3 : f b3 = b3') (hB4 : f b4 = b4') (hB6 : f b6 = b6') :
    Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f)) ≫
      (factorRatioLaurentIso W ha s b3 b4 b6 I hI hs h2 h3 h4 h6).hom =
    (factorRatioLaurentIso U ha' s' b3' b4' b6' J hJ hs' h2' h3' h4' h6').hom ≫
      Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f)) := by
  subst U s' b3' b4' b6'
  exact factorRatioLaurentIso_coefficient f W ha s b3 b4 b6 I J hf hI hJ hs h2 h3 h4 h6

variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

/-- The exact squared-factor Laurent automorphism at the original arithmetic quotient order. -/
def arithmeticFactorRatioLaurentIso : Spec (.of Q[T;T⁻¹]) ≅ Spec (.of Q[T;T⁻¹]) :=
  factorRatioLaurentIso (W.map q) (ha.map q) (q s) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (arithmeticCoefficient_mem π m hs)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
    (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)

local notation "E" => arithmeticFactorRatioLaurentIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "C" => arithmeticInitialFactorRatioChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "G" => arithmeticInitialNodeRestriction π m W s b3 b4 b6 ha h2 h3 h4 h6 hs
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m

/-- The actual full arithmetic boundary is the corrected standard polygon edge. -/
@[reassoc] theorem arithmeticFactorRatioLaurentIso_boundary :
    G ≫ C = (E).hom ≫ PolygonSmoothing.leftBranchOpen Q τ :=
  factorRatioLaurentIso_boundary (W.map q) (ha.map q) (q s) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (arithmeticCoefficient_mem π m hs)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
    (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6) τ
    (initialTangentSmoothing_factor (W.map q) (ha.map q) (q s))

/-- Inverting the exact correction recovers the whole standard arithmetic polygon edge. -/
@[reassoc] theorem arithmeticFactorRatioLaurentIso_inv_boundary :
    (E).inv ≫ G ≫ C = PolygonSmoothing.leftBranchOpen Q τ := by
  rw [arithmeticFactorRatioLaurentIso_boundary, Iso.inv_hom_id_assoc]

local notation "E₁" => arithmeticFactorRatioLaurentIso π (m + 1)
  W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "F" => Spec.map (CommRingCat.ofHom
  (PolygonScalingNaturality.coeffMap (AlgHom.toRingHom (restriction R π m))))
attribute [local irreducible] factorRatioLaurentIso

/-- The full corrected Laurent isomorphism commutes with the actual quotient restriction. -/
@[reassoc] theorem arithmeticFactorRatioLaurentIso_restriction :
    F ≫ (E₁).hom = (E).hom ≫ F := by
  unfold arithmeticFactorRatioLaurentIso
  apply factorRatioLaurentIso_coefficient_of_eq (arithmeticParameterIdeal_restriction R π m)
    (arithmeticInitialCurve_restriction R π m W) ((restriction R π m).commutes s)
    ((restriction R π m).commutes b3) ((restriction R π m).commutes b4)
    ((restriction R π m).commutes b6)

/-- The complete inverse corrected parameter follows the same arithmetic quotient restriction. -/
@[reassoc] theorem arithmeticFactorRatioLaurentIso_inv_restriction :
    F ≫ (E₁).inv = (E).inv ≫ F := by
  apply (cancel_mono (E₁).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [arithmeticFactorRatioLaurentIso_restriction, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassModificationX

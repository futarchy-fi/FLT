/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXStandardPunctureCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXArithmeticPuncture
public import FLT.Mazur.WeierstrassSuccessiveArithmeticRestrictionMaps

/-!
# Full initial standard puncture parameters commute with arithmetic restriction

The square uses the actual consecutive quotient map on Laurent coefficients
and on the entire standard initial D(p), retaining its polynomial corrections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u

/-- Explicit target data keep coefficient transport separate from constructed root reduction. -/
@[reassoc] theorem initialStandardPunctureIso_coefficient_of_eq
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
      (initialStandardPunctureIso W s b3 b4 b6 I hI ha hs h2 h3 h4 h6).hom =
    (initialStandardPunctureIso U s' b3' b4' b6' J hJ ha' hs' h2' h3' h4' h6').hom ≫
      Spec.map (CommRingCat.ofHom (NodalFiber.punctureCoefficientRingMap f s s' hS true)) := by
  subst U s' b3' b4' b6'
  exact initialStandardPunctureIso_coefficient f W s b3 b4 b6 I J hf hI hJ ha hs h2 h3 h4 h6

variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "P" => Spec.map (CommRingCat.ofHom
  (NodalFiber.punctureCoefficientRingMap f (q₁ s) (q₀ s)
    (AlgHom.commutes (restriction R π m) s) true))
local notation "F" => Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f))
local notation "a₀" => arithmeticInitialPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "a₁" => arithmeticInitialPunctureIso π (m + 1) W s b3 b4 b6 ha hs h2 h3 h4 h6

attribute [local irreducible] initialStandardPunctureIso

/-- Every initial standard puncture function follows the original arithmetic restriction. -/
@[reassoc] theorem arithmeticInitialPunctureIso_restriction :
    F ≫ (a₁).hom = (a₀).hom ≫ P := by
  rw [arithmeticInitialPunctureIso, arithmeticInitialPunctureIso]
  apply initialStandardPunctureIso_coefficient_of_eq (arithmeticParameterIdeal_restriction R π m)
  · rw [WeierstrassCurve.map_map]
    exact congrArg W.map (restriction R π m).comp_algebraMap
  · exact (restriction R π m).commutes b3
  · exact (restriction R π m).commutes b4
  · exact (restriction R π m).commutes b6

/-- The inverse original initial parameter also commutes with the complete quotient restriction. -/
@[reassoc] theorem arithmeticInitialPunctureIso_inv_restriction :
    P ≫ (a₁).inv = (a₀).inv ≫ F := by
  have h := arithmeticInitialPunctureIso_restriction π m W s b3 b4 b6 ha hs h2 h3 h4 h6
  have he := congrArg (fun g ↦ (a₀).inv ≫ g ≫ (a₁).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using he.symm

end FLT.Mazur.WeierstrassModificationX

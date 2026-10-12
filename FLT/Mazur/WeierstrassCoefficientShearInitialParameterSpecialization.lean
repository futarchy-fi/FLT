/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialConicSpecialization
public import FLT.Mazur.WeierstrassConicFullParameterCoefficient
public import FLT.Mazur.WeierstrassCoefficientShearConicParameters

/-!
# Arbitrary-root specialization of both complete initial parameters

The full parameter opens map into the actual initial coefficient conic.
Their geometric specialization retains both ordered origins and all regular functions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (f : S →ₐ[R] T) (r : S) (t : T)
  (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (gs : algebraMap R T (π ^ start) = 0)
  (g3 : algebraMap R T (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (g4 : algebraMap R T (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (gt : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "b" => (rootShearCurve (W.map (algebraMap R T)) t).a₁
local notation "c" => algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "d" => algebraMap R T (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "CS" => coefficientShearInitialConic hπ data S r j hj hs h3 h4 hr
local notation "CT" => coefficientShearInitialConic hπ data T t j hj gs g3 g4 gt
local notation "M" => coefficientShearSpecialization hπ data S T r t j hj f
variable (hrt : f r = t)
local notation "ha" => rootShearTangent_coefficient W S r T f t hrt
local notation "hc" => f.commutes (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "p" => Spec.map (CommRingCat.ofHom (conicCoefficientMap f.toRingHom a c b d ha hc))


variable (ua : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (ub : IsUnit (rootShearCurve (W.map (algebraMap R T)) t).a₁)
local notation "q" => Spec.map
  (CommRingCat.ofHom (conicParameterCoefficientMap f.toRingHom c d hc))

include hrt in
/-- Specialization preserves the full first initial parameter, including its origin. -/
@[reassoc] theorem coefficientShearSpecialization_initialFirstParameter :
    coefficientConicFirstParameter b d ub CT ≫ M =
      q ≫ coefficientConicFirstParameter a c ua CS := by
  rw [coefficientConicFirstParameter, Category.assoc, Category.assoc,
    coefficientShearSpecialization_initialConic hπ data S T f r t j hj
      hs h3 h4 hr gs g3 g4 gt hrt,
    conicFirstParameter_coefficient_assoc f.toRingHom a c b d ha hc ua ub]
  rfl

include hrt in
/-- Specialization preserves the full opposite initial parameter and its signed slope. -/
@[reassoc] theorem coefficientShearSpecialization_initialSecondParameter :
    coefficientConicSecondParameter b d ub CT ≫ M =
      q ≫ coefficientConicSecondParameter a c ua CS := by
  rw [coefficientConicSecondParameter, Category.assoc, Category.assoc,
    coefficientShearSpecialization_initialConic hπ data S T f r t j hj
      hs h3 h4 hr gs g3 g4 gt hrt,
    conicSecondParameter_coefficient_assoc f.toRingHom a c b d ha hc ua ub]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

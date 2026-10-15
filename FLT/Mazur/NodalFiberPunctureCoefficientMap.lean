/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberCoefficientRingMap
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Coefficient restriction on both complete standard node punctures

Localizing the original coefficient map preserves the Boolean label and every
node function. Taking spectra gives the actual puncture inclusion square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.NodalFiber
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (c : R) (d : S) (hc : f c = d) (opposite : Bool)
local notation "δ" => ite (opposite = true) (p c) (q c)
local notation "δ'" => ite (opposite = true) (p d) (q d)
local notation "L" => Localization.Away δ
local notation "L'" => Localization.Away δ'
local notation "N" => coefficientRingMap f c d hc

/-- The full node coefficient map preserves the selected puncture coordinate. -/
theorem coefficientRingMap_selected : N δ = δ' := by
  cases opposite <;> simp only [Bool.false_eq_true, ↓reduceIte, coefficientRingMap_p,
    coefficientRingMap_q]

/-- Restrict the original coefficient homomorphism to either complete standard puncture. -/
def punctureCoefficientRingMap : L →+* L' :=
  IsLocalization.Away.lift δ (g := (algebraMap (Coordinate d) L').comp N) (by
    rw [RingHom.comp_apply, coefficientRingMap_selected]
    exact IsLocalization.Away.algebraMap_isUnit δ')

/-- Every full node function restricts through the original coefficient map. -/
@[simp] theorem punctureCoefficientRingMap_base (z : Coordinate c) :
    punctureCoefficientRingMap f c d hc opposite (algebraMap (Coordinate c) L z) =
      algebraMap (Coordinate d) L' (N z) :=
  IsLocalization.Away.lift_eq _ _ _

/-- The complete first corrected parameter restricts without replacing it by a monomial. -/
theorem punctureCoefficientRingMap_p :
    punctureCoefficientRingMap f c d hc opposite (algebraMap (Coordinate c) L (p c)) =
      algebraMap (Coordinate d) L' (p d) := by
  rw [punctureCoefficientRingMap_base, coefficientRingMap_p]

/-- The complete opposite corrected parameter also restricts unchanged. -/
theorem punctureCoefficientRingMap_q :
    punctureCoefficientRingMap f c d hc opposite (algebraMap (Coordinate c) L (q c)) =
      algebraMap (Coordinate d) L' (q d) := by
  rw [punctureCoefficientRingMap_base, coefficientRingMap_q]

/-- The original coefficient restriction commutes with the entire puncture inclusions. -/
@[reassoc] theorem punctureCoefficientRingMap_square :
    Spec.map (CommRingCat.ofHom (punctureCoefficientRingMap f c d hc opposite)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Coordinate c) L)) =
    Spec.map (CommRingCat.ofHom (algebraMap (Coordinate d) L')) ≫
      Spec.map (CommRingCat.ofHom N) := by
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g))
  exact RingHom.ext (punctureCoefficientRingMap_base f c d hc opposite)

end FLT.Mazur.NodalFiber

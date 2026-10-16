/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioLaurent

/-!
# The corrected polygon parameter on the full original initial puncture

The inverse squared-factor Laurent automorphism reparametrizes the existing
isomorphism onto the entire original D(p), preserving its arithmetic restrictions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "D" => Localization.Away (NodalFiber.p (q s))
local notation "E" => arithmeticFactorRatioLaurentIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "P" => arithmeticInitialPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "G" => arithmeticInitialNodeRestriction π m W s b3 b4 b6 ha h2 h3 h4 h6 hs
local notation "C" => arithmeticInitialFactorRatioChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "i" => arithmeticInitialPunctureInclusion π m W s ha hs

/-- The full original initial puncture with exactly the corrected polygon Laurent parameter. -/
def arithmeticFactorRatioPunctureIso : Spec (.of Q[T;T⁻¹]) ≅ Spec (.of D) :=
  (E).symm ≪≫ P
local notation "P'" => arithmeticFactorRatioPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6

/-- The original full node boundary retains the complete inverse squared-factor correction. -/
@[reassoc] theorem arithmeticFactorRatioPunctureIso_node_boundary :
    (P').hom ≫ i = (E).inv ≫ G := by
  change ((E).inv ≫ (P).hom) ≫ i = _
  rw [Category.assoc, arithmeticInitialPunctureIso_boundary]

/-- The whole original puncture is precisely the standard edge of the corrected polygon chart. -/
@[reassoc] theorem arithmeticFactorRatioPunctureIso_polygon_boundary :
    (P').hom ≫ i ≫ C =
      PolygonSmoothing.leftBranchOpen Q (arithmeticInitialMobiusSmoothing W ha s π m) := by
  rw [← Category.assoc, arithmeticFactorRatioPunctureIso_node_boundary, Category.assoc,
    arithmeticFactorRatioLaurentIso_inv_boundary]

local notation "E₁" => arithmeticFactorRatioLaurentIso π (m + 1)
  W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "P₁" => arithmeticInitialPunctureIso π (m + 1)
  W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "P₁'" => arithmeticFactorRatioPunctureIso π (m + 1)
  W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "F" => Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f))
local notation "d" => Spec.map (CommRingCat.ofHom
  (NodalFiber.punctureCoefficientRingMap f (algebraMap R (Quotient R π (m + 1)) s) (q s)
    (AlgHom.commutes (restriction R π m) s) true))

/-- Every corrected initial puncture function follows the actual arithmetic quotient map. -/
@[reassoc] theorem arithmeticFactorRatioPunctureIso_restriction :
    F ≫ (P₁').hom = (P').hom ≫ d := by
  change F ≫ (E₁).inv ≫ (P₁).hom = ((E).inv ≫ (P).hom) ≫ d
  rw [← Category.assoc, arithmeticFactorRatioLaurentIso_inv_restriction,
    Category.assoc, arithmeticInitialPunctureIso_restriction, Category.assoc]

/-- The inverse full puncture identification also preserves the actual quotient restriction. -/
@[reassoc] theorem arithmeticFactorRatioPunctureIso_inv_restriction :
    d ≫ (P₁').inv = (P').inv ≫ F := by
  apply (cancel_mono (P₁').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [arithmeticFactorRatioPunctureIso_restriction, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassModificationX

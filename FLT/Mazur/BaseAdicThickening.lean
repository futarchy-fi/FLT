/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackIdeal
public import FLT.Mazur.PolygonDivisorPowerPullback

/-!
# Base-ideal thickenings

Powers of the extended base ideal define the actual base-changed closed
subschemes. On an affine base, their affine ideals are extensions of the
ordinary ideal powers, including the maximal ideal of a local ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.BaseAdicThickening

variable {X S : Scheme.{u}}

/-- Equality of ideals gives the comparison of their actual closed subschemes. -/
def subschemeCongr {I J : X.IdealSheafData} (h : I = J) : I.subscheme ≅ J.subscheme :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme h)

@[reassoc (attr := simp)]
lemma subschemeCongr_hom_ι {I J : X.IdealSheafData} (h : I = J) :
    (subschemeCongr h).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp [subschemeCongr]

/-- The ideal-power thickening is the base change of the base's thickening. -/
def powerPullbackIso (J : S.IdealSheafData) (f : X ⟶ S) (n : ℕ) :
    (J.comap f ^ n).subscheme ≅ pullback f (J ^ n).subschemeι :=
  subschemeCongr (idealSheaf_comap_pow J f n).symm ≪≫ (J ^ n).comapIso f

/-- The thickening comparison retains its actual immersion in X. -/
@[reassoc (attr := simp)]
lemma powerPullbackIso_hom_fst (J : S.IdealSheafData) (f : X ⟶ S) (n : ℕ) :
    (powerPullbackIso J f n).hom ≫ pullback.fst f (J ^ n).subschemeι =
      (J.comap f ^ n).subschemeι := by
  simp [powerPullbackIso]

/-- The ideal sheaf of an ideal of the affine base ring. -/
def baseIdeal (R : CommRingCat.{u}) (J : Ideal R) : (Spec R).IdealSheafData :=
  ofIdealTop (J.map (Scheme.ΓSpecIso R).inv.hom)

/-- The specified base ideal has exactly its original coordinate-ring ideal. -/
@[simp]
lemma baseIdeal_top (R : CommRingCat.{u}) (J : Ideal R) :
    (baseIdeal R J).ideal ⟨⊤, isAffineOpen_top _⟩ =
      J.map (Scheme.ΓSpecIso R).inv.hom := by
  simp [baseIdeal]

/-- Passing from ring ideals to ideal sheaves preserves powers. -/
lemma baseIdeal_pow (R : CommRingCat.{u}) (J : Ideal R) (n : ℕ) :
    baseIdeal R (J ^ n) = baseIdeal R J ^ n := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [baseIdeal_top, ideal_pow, Pi.pow_apply, Ideal.map_pow]

/-- On every affine chart the thickening ideal is the extended base-ideal power. -/
lemma extendedPower_ideal {R : CommRingCat.{u}} (J : Ideal R) (f : X ⟶ Spec R)
    (U : X.affineOpens) (n : ℕ) :
    ((baseIdeal R J).comap f ^ n).ideal U =
      (J ^ n).map ((f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso R).inv.hom) := by
  rw [← idealSheaf_comap_pow, ← baseIdeal_pow]
  rw [ideal_comap _ f ⟨⊤, isAffineOpen_top _⟩ U (by simp), baseIdeal_top, Ideal.map_map]

/-- The maximal-ideal thickening uses the actual maximal ideal of the base ring. -/
abbrev maximalIdeal {R : CommRingCat.{u}} [IsLocalRing R] (f : X ⟶ Spec R) :
    X.IdealSheafData := (baseIdeal R (IsLocalRing.maximalIdeal R)).comap f

/-- Maximal-ideal powers cut out the base change of the corresponding base thickenings. -/
def maximalPowerPullbackIso {R : CommRingCat.{u}} [IsLocalRing R]
    (f : X ⟶ Spec R) (n : ℕ) :
    (maximalIdeal f ^ n).subscheme ≅
      pullback f (baseIdeal R (IsLocalRing.maximalIdeal R) ^ n).subschemeι :=
  powerPullbackIso _ f n

end FLT.Mazur.BaseAdicThickening

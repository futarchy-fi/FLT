/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairSecantGeometry
public import FLT.Mazur.WeierstrassDividedReciprocalOutput
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The divided reciprocal is an actual open in the product of divided charts

The ordinate-difference localization embeds in the same relative product as the
secant chart, retaining both exact input projections without inverting the scale.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "H" => Coordinate W s b3 b4 b6
local notation "P" => DividedPairRing W s b3 b4 b6
/-- The ordinate-difference localization of the entire universal divided pair. -/
abbrev DividedPairReciprocalRing := DividedReciprocalRing W s b3 b4 b6
  (dividedPairLeft W s b3 b4 b6) (dividedPairRight W s b3 b4 b6)

local notation "T" => DividedPairReciprocalRing W s b3 b4 b6
local notation "base" => Spec.map (CommRingCat.ofHom (algebraMap R H))
local notation "a" => dividedPairLeft W s b3 b4 b6
local notation "c" => dividedPairRight W s b3 b4 b6

/-- The actual divided reciprocal localization inclusion. -/
def dividedPairReciprocalInclusion : Spec (.of T) ⟶ Spec (.of P) :=
  Spec.map (CommRingCat.ofHom (algebraMap P T))

instance dividedPairReciprocalInclusion_open :
    IsOpenImmersion (dividedPairReciprocalInclusion W s b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (a (y W s b3 b4 b6) - c (y W s b3 b4 b6))

/-- The constructed reciprocal domain embeds in the full relative product. -/
def dividedPairReciprocalToProduct : Spec (.of T) ⟶ pullback base base :=
  dividedPairReciprocalInclusion W s b3 b4 b6 ≫ (dividedPairSpecIso W s b3 b4 b6).inv

instance dividedPairReciprocalToProduct_open :
    IsOpenImmersion (dividedPairReciprocalToProduct W s b3 b4 b6) := by
  unfold dividedPairReciprocalToProduct
  infer_instance

/-- The new domain retains every function of the first divided input. -/
@[reassoc] theorem dividedPairReciprocalToProduct_fst :
    dividedPairReciprocalToProduct W s b3 b4 b6 ≫ pullback.fst base base =
      Spec.map (CommRingCat.ofHom
        (((IsScalarTower.toAlgHom R P T).comp a).toRingHom)) := by
  rw [dividedPairReciprocalToProduct, Category.assoc, dividedPairSpecIso_fst,
    dividedPairReciprocalInclusion, ← Spec.map_comp]
  rfl

/-- The new domain retains every function of the second divided input. -/
@[reassoc] theorem dividedPairReciprocalToProduct_snd :
    dividedPairReciprocalToProduct W s b3 b4 b6 ≫ pullback.snd base base =
      Spec.map (CommRingCat.ofHom
        (((IsScalarTower.toAlgHom R P T).comp c).toRingHom)) := by
  rw [dividedPairReciprocalToProduct, Category.assoc, dividedPairSpecIso_snd,
    dividedPairReciprocalInclusion, ← Spec.map_comp]
  rfl

/-- Localize the output ordinate as well, retaining the full input pair. -/
abbrev DividedPairReciprocalOutputRing := DividedReciprocalOutputRing W s b3 b4 b6 a c

local notation "O" => DividedPairReciprocalOutputRing W s b3 b4 b6

/-- The second genuine principal-open inclusion normalizes the output ordinate. -/
def dividedPairReciprocalOutputInclusion : Spec (.of O) ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T O))

instance dividedPairReciprocalOutputInclusion_open :
    IsOpenImmersion (dividedPairReciprocalOutputInclusion W s b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (dividedReciprocalCoordinates W s b3 b4 b6 a c 1)

/-- The actual reciprocal output domain is an open of the same full divided product. -/
def dividedPairReciprocalOutputToProduct : Spec (.of O) ⟶ pullback base base :=
  dividedPairReciprocalOutputInclusion W s b3 b4 b6 ≫
    dividedPairReciprocalToProduct W s b3 b4 b6

instance dividedPairReciprocalOutputToProduct_open :
    IsOpenImmersion (dividedPairReciprocalOutputToProduct W s b3 b4 b6) := by
  unfold dividedPairReciprocalOutputToProduct
  infer_instance

/-- Output normalization preserves the entire first input map. -/
@[reassoc] theorem dividedPairReciprocalOutputToProduct_fst :
    dividedPairReciprocalOutputToProduct W s b3 b4 b6 ≫ pullback.fst base base =
      Spec.map (CommRingCat.ofHom
        ((IsScalarTower.toAlgHom R T O).comp
          ((IsScalarTower.toAlgHom R P T).comp a)).toRingHom) := by
  rw [dividedPairReciprocalOutputToProduct, Category.assoc, dividedPairReciprocalToProduct_fst,
    dividedPairReciprocalOutputInclusion, ← Spec.map_comp]
  rfl

/-- Output normalization preserves the entire second input map. -/
@[reassoc] theorem dividedPairReciprocalOutputToProduct_snd :
    dividedPairReciprocalOutputToProduct W s b3 b4 b6 ≫ pullback.snd base base =
      Spec.map (CommRingCat.ofHom
        ((IsScalarTower.toAlgHom R T O).comp
          ((IsScalarTower.toAlgHom R P T).comp c)).toRingHom) := by
  rw [dividedPairReciprocalOutputToProduct, Category.assoc, dividedPairReciprocalToProduct_snd,
    dividedPairReciprocalOutputInclusion, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDilatation

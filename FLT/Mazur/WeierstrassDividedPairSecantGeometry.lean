/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairSecant
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The divided secant is an actual open in the product of divided charts

Identify the universal tensor spectrum with the relative product. The secant
localization embeds openly, retaining both exact projection maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local semireducible] DividedPairRing
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "H" => Coordinate W s b3 b4 b6
local notation "P" => DividedPairRing W s b3 b4 b6
local notation "T" => DividedPairSecantRing W s b3 b4 b6
local notation "base" => Spec.map (CommRingCat.ofHom (algebraMap R H))
local notation "a" => dividedPairLeft W s b3 b4 b6
local notation "c" => dividedPairRight W s b3 b4 b6

/-- The tensor spectrum is precisely the relative product of the two original divided charts. -/
def dividedPairSpecIso : pullback base base ≅ Spec (.of P) := by
  unfold DividedPairRing
  exact pullbackSpecIso R H H

/-- The first projection is the original first tensor inclusion. -/
@[reassoc] theorem dividedPairSpecIso_fst :
    (dividedPairSpecIso W s b3 b4 b6).inv ≫ pullback.fst base base =
      Spec.map (CommRingCat.ofHom (a).toRingHom) :=
  pullbackSpecIso_inv_fst R H H

/-- The second projection is the original second tensor inclusion. -/
@[reassoc] theorem dividedPairSpecIso_snd :
    (dividedPairSpecIso W s b3 b4 b6).inv ≫ pullback.snd base base =
      Spec.map (CommRingCat.ofHom (c).toRingHom) :=
  pullbackSpecIso_inv_snd R H H

/-- The actual divided secant localization inclusion. -/
def dividedPairSecantInclusion : Spec (.of T) ⟶ Spec (.of P) :=
  Spec.map (CommRingCat.ofHom (algebraMap P T))

instance dividedPairSecantInclusion_open :
    IsOpenImmersion (dividedPairSecantInclusion W s b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (a (x W s b3 b4 b6) - c (x W s b3 b4 b6))

/-- The constructed secant domain embeds in the full relative product. -/
def dividedPairSecantToProduct : Spec (.of T) ⟶ pullback base base :=
  dividedPairSecantInclusion W s b3 b4 b6 ≫ (dividedPairSpecIso W s b3 b4 b6).inv

instance dividedPairSecantToProduct_open :
    IsOpenImmersion (dividedPairSecantToProduct W s b3 b4 b6) := by
  unfold dividedPairSecantToProduct
  infer_instance

/-- The new domain retains every function of the first divided input. -/
@[reassoc] theorem dividedPairSecantToProduct_fst :
    dividedPairSecantToProduct W s b3 b4 b6 ≫ pullback.fst base base =
      Spec.map (CommRingCat.ofHom
        (((IsScalarTower.toAlgHom R P T).comp a).toRingHom)) := by
  rw [dividedPairSecantToProduct, Category.assoc, dividedPairSpecIso_fst,
    dividedPairSecantInclusion, ← Spec.map_comp]
  rfl

/-- The new domain retains every function of the second divided input. -/
@[reassoc] theorem dividedPairSecantToProduct_snd :
    dividedPairSecantToProduct W s b3 b4 b6 ≫ pullback.snd base base =
      Spec.map (CommRingCat.ofHom
        (((IsScalarTower.toAlgHom R P T).comp c).toRingHom)) := by
  rw [dividedPairSecantToProduct, Category.assoc, dividedPairSpecIso_snd,
    dividedPairSecantInclusion, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDilatation

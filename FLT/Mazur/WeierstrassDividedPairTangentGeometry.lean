/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairSecantGeometry
public import FLT.Mazur.WeierstrassDividedTangentSource
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The divided tangent is an actual open in the product of divided charts

The second-slope localization embeds in the same relative product as the
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
/-- The second-slope localization of the entire universal divided pair. -/
abbrev DividedPairTangentRing := DividedTangentRing W s b3 b4 b6
  (dividedPairLeft W s b3 b4 b6) (dividedPairRight W s b3 b4 b6)

local notation "T" => DividedPairTangentRing W s b3 b4 b6
local notation "base" => Spec.map (CommRingCat.ofHom (algebraMap R H))
local notation "a" => dividedPairLeft W s b3 b4 b6
local notation "c" => dividedPairRight W s b3 b4 b6

/-- The actual divided tangent localization inclusion. -/
def dividedPairTangentInclusion : Spec (.of T) ⟶ Spec (.of P) :=
  Spec.map (CommRingCat.ofHom (algebraMap P T))

instance dividedPairTangentInclusion_open :
    IsOpenImmersion (dividedPairTangentInclusion W s b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (dividedTangentDenominator W s b3 b4 b6 a c)

/-- The constructed tangent domain embeds in the full relative product. -/
def dividedPairTangentToProduct : Spec (.of T) ⟶ pullback base base :=
  dividedPairTangentInclusion W s b3 b4 b6 ≫ (dividedPairSpecIso W s b3 b4 b6).inv

instance dividedPairTangentToProduct_open :
    IsOpenImmersion (dividedPairTangentToProduct W s b3 b4 b6) := by
  unfold dividedPairTangentToProduct
  infer_instance

/-- The new domain retains every function of the first divided input. -/
@[reassoc] theorem dividedPairTangentToProduct_fst :
    dividedPairTangentToProduct W s b3 b4 b6 ≫ pullback.fst base base =
      Spec.map (CommRingCat.ofHom
        (((IsScalarTower.toAlgHom R P T).comp a).toRingHom)) := by
  rw [dividedPairTangentToProduct, Category.assoc, dividedPairSpecIso_fst,
    dividedPairTangentInclusion, ← Spec.map_comp]
  rfl

/-- The new domain retains every function of the second divided input. -/
@[reassoc] theorem dividedPairTangentToProduct_snd :
    dividedPairTangentToProduct W s b3 b4 b6 ≫ pullback.snd base base =
      Spec.map (CommRingCat.ofHom
        (((IsScalarTower.toAlgHom R P T).comp c).toRingHom)) := by
  rw [dividedPairTangentToProduct, Category.assoc, dividedPairSpecIso_snd,
    dividedPairTangentInclusion, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDilatation

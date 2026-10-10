/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineMorphismExt
public import FLT.Mazur.WeierstrassIntegralProductOverlap
public import FLT.Mazur.WeierstrassReciprocalOutputRegular

/-!
# The actual secant chart detects morphisms from the entire cubic product

Regular input coordinates make every simultaneous affine overlap
schematically dense. The regular X difference then permits restriction to
the secant open. Both steps retain nilpotents in the coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Both charts in the original two-chart cover are flat over the base. -/
theorem productInputChart_flat (b : Bool) :
    Module.Flat R (Coordinate W (productChartCoordinate b)) := by
  cases b
  · exact affineChart_flat W
  · exact infinityChart_flat W

/-- Each input's restriction to the affine overlap is injective. -/
theorem productInputOverlap_injective (b : Bool) :
    Function.Injective (overlapRestriction W (productChartCoordinate b) 2) := by
  apply IsLocalization.injective (Overlap W (productChartCoordinate b) 2)
    (M := Submonoid.powers (coord W (productChartCoordinate b) 2))
  rintro x ⟨n, rfl⟩
  apply IsRegular.mem_nonZeroDivisors
  apply IsRegular.pow
  cases b
  · change IsRegular (coord W 2 2)
    rw [coord_self]
    exact isRegular_one
  · exact infinityChart_coord_z_regular W

/-- Every simultaneous affine input overlap is injective on its original coordinate ring. -/
theorem productAffineOverlap_injective (b c : Bool) :
    Function.Injective (productOverlapRestriction W (productChartCoordinate b)
      (productChartCoordinate c) 2 2) := by
  let _ := productInputChart_flat W b
  let _ := productInputChart_flat W c
  let _ : Module.Flat R (Overlap W (productChartCoordinate c) 2) :=
    Module.Flat.trans R (Coordinate W (productChartCoordinate c)) _
  exact TensorProduct.map_injective_of_flat_flat
    (overlapRestriction W (productChartCoordinate b) 2).toLinearMap
    (overlapRestriction W (productChartCoordinate c) 2).toLinearMap
    (productInputOverlap_injective W b) (productInputOverlap_injective W c)

/-- The affine input product determines morphisms to any separated target over the base. -/
theorem integralCurveProduct_hom_ext_affine {X S : Scheme.{u}} (s : X ⟶ S) [IsSeparated s]
    (f g : integralCurveProduct W ⟶ X) (hb : f ≫ s = g ≫ s)
    (ha : integralCurveProductChart W false false ≫ f =
      integralCurveProductChart W false false ≫ g) : f = g := by
  apply (integralCurveProductCover W).hom_ext
  rintro ⟨b, c⟩
  change integralCurveProductChart W b c ≫ f = integralCurveProductChart W b c ≫ g
  let _ : IsSchemeTheoreticallyDominant
      (integralProductOverlapFst W b c false false) :=
    SurjectiveDominantEpi.spec_schematic
      (productOverlapRestriction W (productChartCoordinate b)
        (productChartCoordinate c) 2 2).toRingHom (productAffineOverlap_injective W b c)
  apply Chow.schematicallyDense_ext s
    (by simpa only [Category.assoc] using congrArg (integralCurveProductChart W b c ≫ ·) hb)
    (integralProductOverlapFst W b c false false)
  rw [← Category.assoc, ← Category.assoc, integralProductOverlap_condition]
  simpa only [Category.assoc] using
    congrArg (integralProductOverlapSnd W b c false false ≫ ·) ha

/-- The actual secant restriction is injective on functions. -/
theorem secantRestriction_injective : Function.Injective (secantRestriction W) := by
  apply IsLocalization.injective (SecantChart W) (M := Submonoid.powers (secantDenominator W))
  rintro x ⟨n, rfl⟩
  exact ((secantDenominator_regular W).pow n).mem_nonZeroDivisors

/-- Equality on the actual secant open determines the whole product morphism. -/
theorem integralCurveProduct_hom_ext_secant {X S : Scheme.{u}} (s : X ⟶ S) [IsSeparated s]
    (f g : integralCurveProduct W ⟶ X) (hb : f ≫ s = g ≫ s)
    (hs : Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫
        integralCurveProductChart W false false ≫ f =
      Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫
        integralCurveProductChart W false false ≫ g) : f = g := by
  apply integralCurveProduct_hom_ext_affine W s f g hb
  let _ := SurjectiveDominantEpi.spec_schematic (secantRestriction W).toRingHom
    (secantRestriction_injective W)
  exact Chow.schematicallyDense_ext s
    (by simpa only [Category.assoc] using
      congrArg (integralCurveProductChart W false false ≫ ·) hb)
    (Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom)) hs

end FLT.Mazur.WeierstrassIntegralChart

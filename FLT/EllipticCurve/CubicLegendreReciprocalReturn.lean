/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCoefficientNaturality
public import FLT.EllipticCurve.CubicLegendreCyclicInvolutions

/-! # The descended reciprocal return map

The coordinate map on the inverse-parameter root cover descends to a return
map on cyclic parameters. Coefficient naturality and the local inverse
coordinate product prove its composition with the original descended map is
the identity. Both inverse laws hold, and the actual return map is identified
with the inverse of the previously constructed isomorphism over the base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (W V : WeierstrassCurve R) [W.IsElliptic] [V.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
variable (d : Rˣ) [Fact (IsUnit (2 : R))]
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]
variable (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
variable (hd : legendreReciprocalChange (quadraticEtaleUnit d) •
  W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d)))

/-- The descended cyclic map for a pure reciprocal coordinate scaling. -/
def quadraticReciprocalDesc :
    (scalarQuotientModel V p).left ⟶ (scalarQuotientModel W p).left :=
  quadraticCoordinateDesc W p d V ha₁ ha₃ 0
    (by simpa only [map_zero, signCoordinateChange, legendreReciprocalChange] using hd)

/-- The descended scaling recovers the actual local cyclic transport. -/
theorem quadraticReciprocalDesc_fac :
    coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p ≫
      quadraticReciprocalDesc W V p d ha₁ ha₃ hd =
    (groupCyclicParameterIso p (variableChangeCongrOverIso
      (W.map (algebraMap R (QuadraticEtaleRing d)))
      (V.map (algebraMap R (QuadraticEtaleRing d)))
      (legendreReciprocalChange (quadraticEtaleUnit d)) hd)).hom.left ≫
        coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p := by
  simpa only [quadraticReciprocalDesc, map_zero, signCoordinateChange,
    legendreReciprocalChange] using quadraticCoordinateDesc_fac W p d V ha₁ ha₃ 0
      (by simpa only [map_zero, signCoordinateChange, legendreReciprocalChange] using hd)

local instance : IsNoetherianRing (QuadraticEtaleRing d⁻¹) :=
  quadraticReciprocal_isNoetherian d
local instance : IsDomain (QuadraticEtaleRing d⁻¹) := quadraticReciprocal_isDomain d
local instance : Fact (IsUnit (p : QuadraticEtaleRing d⁻¹)) :=
  ⟨by simpa only [map_natCast] using
    (Fact.out : IsUnit (p : QuadraticEtaleRing d)).map (quadraticReciprocalHom d)⟩

variable (hv₁ : V.a₁ = 0) (hv₃ : V.a₃ = 0)
variable (hb : legendreReciprocalChange (quadraticEtaleUnit d⁻¹) •
  V.map (algebraMap R (QuadraticEtaleRing d⁻¹)) = W.map (algebraMap R (QuadraticEtaleRing d⁻¹)))

/-- The return scaling on the reciprocal cover followed by the original is identity. -/
theorem quadraticReciprocalDesc_return_comp :
    quadraticReciprocalDesc V W p d⁻¹ hv₁ hv₃ hb ≫
      quadraticReciprocalDesc W V p d ha₁ ha₃ hd = 𝟙 _ := by
  have hl := variableChangeCyclic_trans_of_product_one
    (W.map (algebraMap R (QuadraticEtaleRing d⁻¹))) p
    (V.map (algebraMap R (QuadraticEtaleRing d⁻¹)))
    (legendreReciprocalChange (quadraticEtaleUnit d⁻¹))
    (legendreReciprocalChange (quadraticEtaleUnit d⁻¹)⁻¹)
    (quadraticReciprocalChange_equation W V d hd) hb
    (by simpa only [inv_inv] using legendreReciprocalChange_inv_mul (quadraticEtaleUnit d⁻¹)⁻¹)
  have hh := congrArg (fun e => e.hom.left) hl
  simp only [Iso.trans_hom, Over.comp_left, Iso.refl_hom, Over.id_left] at hh
  have hlast := congrArg (fun m => m ≫ (quadraticReciprocalCyclicIso W p d).hom ≫
    coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p) hh
  simp only [Category.assoc, Category.id_comp] at hlast
  have hn := congrArg (fun m => m ≫ coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p)
    (quadraticReciprocalChange_cyclic W V d hd p)
  simp only [Category.assoc] at hn
  apply (cancel_epi (coefficientScalarQuotientMorphism W (QuadraticEtaleRing d⁻¹) p)).mp
  rw [← Category.assoc, quadraticReciprocalDesc_fac, Category.assoc,
    ← quadraticReciprocalCyclicIso_coefficient V p d, Category.assoc,
    quadraticReciprocalDesc_fac, hn, hlast, quadraticReciprocalCyclicIso_coefficient,
    Category.comp_id]

instance quadraticReciprocalDesc_isIso :
    IsIso (quadraticReciprocalDesc W V p d ha₁ ha₃ hd) :=
  quadraticCoordinateDescIsIso W V p d ha₁ ha₃ 0
    (by simpa only [map_zero, signCoordinateChange, legendreReciprocalChange] using hd)

/-- The original descended scaling followed by the return is identity. -/
theorem quadraticReciprocalDesc_comp_return :
    quadraticReciprocalDesc W V p d ha₁ ha₃ hd ≫
      quadraticReciprocalDesc V W p d⁻¹ hv₁ hv₃ hb = 𝟙 _ := by
  apply (cancel_mono (quadraticReciprocalDesc W V p d ha₁ ha₃ hd)).mp
  rw [Category.assoc, quadraticReciprocalDesc_return_comp, Category.comp_id, Category.id_comp]

/-- The descended reciprocal scaling preserves the coefficient base. -/
theorem quadraticReciprocalDesc_toBase :
    quadraticReciprocalDesc W V p d ha₁ ha₃ hd ≫ (scalarQuotientModel W p).hom =
      (scalarQuotientModel V p).hom :=
  quadraticCoordinateDesc_toBase W p d V ha₁ ha₃ 0
    (by simpa only [map_zero, signCoordinateChange, legendreReciprocalChange] using hd)

section Universal
/-- The root cover of the inverse universal Legendre parameter. -/
abbrev LegendreReciprocalReturnRing (p : ℕ) :=
  QuadraticEtaleRing (legendreParameterUnit p)⁻¹

instance legendreReciprocalReturnNoetherian (p : ℕ) :
    IsNoetherianRing (LegendreReciprocalReturnRing p) :=
  quadraticReciprocal_isNoetherian (legendreParameterUnit p)

instance legendreReciprocalReturnDomain (p : ℕ) [NeZero p] :
    IsDomain (LegendreReciprocalReturnRing p) :=
  quadraticReciprocal_isDomain (legendreParameterUnit p)

instance legendreReciprocalReturnLevelUnit (p : ℕ) :
    Fact (IsUnit (p : LegendreReciprocalReturnRing p)) :=
  ⟨by
    simpa only [map_natCast] using
      (Fact.out : IsUnit (p : LegendreUniversalReciprocalRing p)).map
        (quadraticReciprocalHom (legendreParameterUnit p))⟩

/-- The reciprocal root on the inverse-parameter cover returns the original equation. -/
theorem legendreReciprocal_return_equation (p : ℕ) :
    legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p)⁻¹) •
      (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)).map
        (algebraMap (LegendreBase p) (LegendreReciprocalReturnRing p)) =
      (legendreModel p).map (algebraMap (LegendreBase p) (LegendreReciprocalReturnRing p)) := by
  have h := legendreReciprocalChange_curve
    (Units.map (algebraMap (LegendreBase p) (LegendreReciprocalReturnRing p)).toMonoidHom
      (legendreParameterUnit p)⁻¹)
    (quadraticEtaleUnit (legendreParameterUnit p)⁻¹)
    (quadraticEtaleUnit_square (legendreParameterUnit p)⁻¹)
  simpa [legendreModel, legendreCurve_map] using h

/-- The actual return map descended from the inverse-parameter root cover. -/
def legendreReciprocalReturnDescendedMap (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel (legendreModel p) p).left ⟶
      (scalarQuotientModel
        (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
        p).left :=
  quadraticReciprocalDesc
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    (legendreModel p) p (legendreParameterUnit p)⁻¹ rfl rfl
    (legendreReciprocal_return_equation p)

/-- The descended return followed by the original reciprocal map is identity. -/
theorem legendreReciprocalReturnDescendedMap_comp (p : ℕ) [Fact p.Prime] :
    legendreReciprocalReturnDescendedMap p ≫ legendreReciprocalDescendedMap p = 𝟙 _ := by
  exact quadraticReciprocalDesc_return_comp (legendreModel p)
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    p (legendreParameterUnit p) rfl rfl
    (by simpa only [map_zero, signCoordinateChange, legendreReciprocalChange] using
      legendreReciprocal_coordinate_equation p)
    rfl rfl (legendreReciprocal_return_equation p)

/-- The original reciprocal map followed by the descended return is identity. -/
theorem legendreReciprocalDescendedMap_comp_return (p : ℕ) [Fact p.Prime] :
    legendreReciprocalDescendedMap p ≫ legendreReciprocalReturnDescendedMap p = 𝟙 _ := by
  exact quadraticReciprocalDesc_comp_return (legendreModel p)
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    p (legendreParameterUnit p) rfl rfl
    (by simpa only [map_zero, signCoordinateChange, legendreReciprocalChange] using
      legendreReciprocal_coordinate_equation p)
    rfl rfl (legendreReciprocal_return_equation p)

/-- The descended return as a morphism over the universal coefficient base. -/
def legendreReciprocalReturnDescendedOver (p : ℕ) [Fact p.Prime] :
    scalarQuotientModel (legendreModel p) p ⟶
      scalarQuotientModel
        (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p :=
  Over.homMk (legendreReciprocalReturnDescendedMap p)
    (quadraticReciprocalDesc_toBase
      (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
      (legendreModel p) p (legendreParameterUnit p)⁻¹ rfl rfl
      (legendreReciprocal_return_equation p))

/-- The explicit descended return is the inverse of the existing reciprocal isomorphism. -/
theorem legendreReciprocalReturnDescendedOver_eq_inv (p : ℕ) [Fact p.Prime] :
    legendreReciprocalReturnDescendedOver p = (legendreReciprocalDescendedIso p).inv := by
  apply (cancel_mono (legendreReciprocalDescendedIso p).hom).mp
  rw [Iso.inv_hom_id]
  apply Over.OverMorphism.ext
  exact legendreReciprocalReturnDescendedMap_comp p

end Universal

end WeierstrassCurve.CubicCharts

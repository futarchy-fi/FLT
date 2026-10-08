/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreBraidLastCover

/-! # The mixed relation for actual descended Legendre maps

Both three-step paths use actual quadratic descended coordinate maps,
with a common final Legendre equation. Their pullbacks to the common
coefficient cover are transports by the corresponding coordinate products.
The local braid identity and the effective epimorphism of the common
cyclic cover prove equality of the two global composites.

This is a relation between the displayed cyclic schemes over the fixed
Legendre base. Packaging the parameter-changing maps into a group action
and constructing a modular quotient are further tasks.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts

instance legendreComplementInverseElliptic (p : ℕ) :
    (legendreCurve
      (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)).IsElliptic :=
  legendreCurve_elliptic _ (legendreBase_units p).1
    (legendreComplementUnit p)⁻¹.isUnit
    (unitInverse_sub_one_isUnit _ (by
      have he : (legendreComplementUnit p : LegendreBase p) - 1 = -legendreParameter p := by
        rw [legendreComplementUnit_val]
        ring
      rw [he]
      exact (legendreBase_units p).2.2.1.neg))

instance legendreBraidEndpointElliptic (p : ℕ) :
    (legendreCurve (1 -
      (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))).IsElliptic := by
  rw [← legendreBraidLast_endpoint]
  infer_instance

instance legendreBraidRightMiddleElliptic (p : ℕ) :
    (legendreCurve (1 -
      (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))).IsElliptic := by
  rw [← legendreBraidLastUnit_val]
  infer_instance

theorem legendreBraidComplement_equation (p : ℕ) :
    signCoordinateChange (quadraticEtaleUnit (legendreComplementUnit p))
      (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreComplementUnit p)) 0) •
        (legendreCurve (1 - legendreParameter p)).map
          (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreComplementUnit p))) =
    (legendreCurve (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)).map
      (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreComplementUnit p))) := by
  have h := legendreReciprocalChange_curve
    (Units.map (algebraMap (LegendreBase p)
      (QuadraticEtaleRing (legendreComplementUnit p))).toMonoidHom (legendreComplementUnit p))
    (quadraticEtaleUnit (legendreComplementUnit p))
    (quadraticEtaleUnit_square (legendreComplementUnit p))
  simpa [signCoordinateChange, legendreReciprocalChange, legendreCurve_map,
    legendreComplementUnit_val] using h

theorem legendreBraidSwap_equation (p : ℕ) (l : LegendreBase p) :
    signCoordinateChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ))
      (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) 1) •
        (legendreCurve l).map (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)) =
    (legendreCurve (1 - l)).map
      (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)) := by
  simp only [map_one, legendreCurve_map, map_sub]
  exact legendreSwapChange_curve _ _ (legendreSwapRoot_square p)

theorem legendreBraidRightLast_equation (p : ℕ) :
    signCoordinateChange (quadraticEtaleUnit (legendreBraidLastUnit p))
      (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreBraidLastUnit p)) 0) •
        (legendreCurve (1 -
          (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))).map
          (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreBraidLastUnit p))) =
    (legendreCurve (1 -
      (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))).map
      (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreBraidLastUnit p))) := by
  simpa only [legendreBraidLastUnit_val, legendreBraidLast_endpoint] using
    legendreBraidLast_equation p

variable (p : ℕ) [Fact p.Prime]

/-- The reciprocal step after the first swap, descended from the complement cover. -/
def legendreBraidComplementDescendedMap :
    (scalarQuotientModel
      (legendreCurve
        (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p).left ⟶
        (scalarQuotientModel (legendreCurve (1 - legendreParameter p)) p).left :=
  quadraticCoordinateDesc (legendreCurve (1 - legendreParameter p))
    p (legendreComplementUnit p)
    (legendreCurve (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    rfl rfl 0 (legendreBraidComplement_equation p)

/-- The last swap in the swap-reciprocal-swap path. -/
def legendreBraidLeftLastMap :
    (scalarQuotientModel (legendreCurve (1 -
      (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))) p).left ⟶
    (scalarQuotientModel
      (legendreCurve
        (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p).left :=
  quadraticCoordinateDesc
    (legendreCurve (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    p (-1 : (LegendreBase p)ˣ)
    (legendreCurve (1 - (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)))
    rfl rfl 1 (legendreBraidSwap_equation p _)

/-- The middle swap in the reciprocal-swap-reciprocal path. -/
def legendreBraidRightMiddleMap :
    (scalarQuotientModel (legendreCurve (1 -
      (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))) p).left ⟶
    (scalarQuotientModel
      (legendreCurve
        (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p).left :=
  quadraticCoordinateDesc
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    p (-1 : (LegendreBase p)ˣ)
    (legendreCurve (1 - (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)))
    rfl rfl 1 (legendreBraidSwap_equation p _)

/-- The final reciprocal step, written with the common endpoint curve. -/
def legendreBraidRightLastMap :
    (scalarQuotientModel (legendreCurve (1 -
      (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))) p).left ⟶
    (scalarQuotientModel (legendreCurve (1 -
      (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))) p).left :=
  quadraticCoordinateDesc
    (legendreCurve (1 - (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)))
    p (legendreBraidLastUnit p)
    (legendreCurve (1 - (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)))
    rfl rfl 0 (legendreBraidRightLast_equation p)

/-- The actual descended swap-reciprocal-swap composite. -/
def legendreBraidLeftComposite :
    (scalarQuotientModel (legendreCurve (1 -
      (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))) p).left ⟶
        (scalarQuotientModel (legendreModel p) p).left :=
  legendreBraidLeftLastMap p ≫ legendreBraidComplementDescendedMap p ≫ legendreSwapDescendedMap p

/-- The actual descended reciprocal-swap-reciprocal composite. -/
def legendreBraidRightComposite :
    (scalarQuotientModel (legendreCurve (1 -
      (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))) p).left ⟶
        (scalarQuotientModel (legendreModel p) p).left :=
  legendreBraidRightLastMap p ≫ legendreBraidRightMiddleMap p ≫ legendreReciprocalDescendedMap p

private theorem composeThreeSquares {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : D}
    (q₀ : Y₀ ⟶ X₀) (q₁ : Y₁ ⟶ X₁) (q₂ : Y₂ ⟶ X₂) (q₃ : Y₃ ⟶ X₃)
    (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    (F : Y₁ ⟶ Y₀) (G : Y₂ ⟶ Y₁) (H : Y₃ ⟶ Y₂)
    (hf : q₁ ≫ f = F ≫ q₀) (hg : q₂ ≫ g = G ≫ q₁) (hh : q₃ ≫ h = H ≫ q₂) :
    q₃ ≫ (h ≫ g ≫ f) = H ≫ G ≫ F ≫ q₀ := by
  rw [← Category.assoc q₃ h, hh, Category.assoc H q₂,
    ← Category.assoc q₂ g, hg, Category.assoc G q₁, hf]

attribute [local irreducible] variableChangeCongrOverIso groupCyclicParameterIso

/-- Three compatible descended maps pull back to transport by the coordinate product. -/
theorem braidCyclic_transport_three
    (W V U Z : WeierstrassCurve (LegendreBase p))
    [W.IsElliptic] [V.IsElliptic] [U.IsElliptic] [Z.IsElliptic]
    (A B C : VariableChange (LegendreBraidRing p))
    (hC : C • W.map (algebraMap (LegendreBase p) (LegendreBraidRing p)) =
      V.map (algebraMap (LegendreBase p) (LegendreBraidRing p)))
    (hB : B • V.map (algebraMap (LegendreBase p) (LegendreBraidRing p)) =
      U.map (algebraMap (LegendreBase p) (LegendreBraidRing p)))
    (hA : A • U.map (algebraMap (LegendreBase p) (LegendreBraidRing p)) =
      Z.map (algebraMap (LegendreBase p) (LegendreBraidRing p)))
    (f : (scalarQuotientModel V p).left ⟶ (scalarQuotientModel W p).left)
    (g : (scalarQuotientModel U p).left ⟶ (scalarQuotientModel V p).left)
    (h : (scalarQuotientModel Z p).left ⟶ (scalarQuotientModel U p).left)
    (hf : coefficientScalarQuotientMorphism V (LegendreBraidRing p) p ≫ f =
      (groupCyclicParameterIso p (variableChangeCongrOverIso _ _ C hC)).hom.left ≫
        coefficientScalarQuotientMorphism W (LegendreBraidRing p) p)
    (hg : coefficientScalarQuotientMorphism U (LegendreBraidRing p) p ≫ g =
      (groupCyclicParameterIso p (variableChangeCongrOverIso _ _ B hB)).hom.left ≫
        coefficientScalarQuotientMorphism V (LegendreBraidRing p) p)
    (hh : coefficientScalarQuotientMorphism Z (LegendreBraidRing p) p ≫ h =
      (groupCyclicParameterIso p (variableChangeCongrOverIso _ _ A hA)).hom.left ≫
        coefficientScalarQuotientMorphism U (LegendreBraidRing p) p) :
    coefficientScalarQuotientMorphism Z (LegendreBraidRing p) p ≫ (h ≫ g ≫ f) =
      (groupCyclicParameterIso p (variableChangeCongrOverIso
        (W.map (algebraMap (LegendreBase p) (LegendreBraidRing p)))
        (Z.map (algebraMap (LegendreBase p) (LegendreBraidRing p))) (A * B * C)
        (by rw [mul_smul, hC, mul_smul, hB, hA]))).hom.left ≫
          coefficientScalarQuotientMorphism W (LegendreBraidRing p) p := by
  have ht := variableChangeCyclic_trans_three p
    (W.map (algebraMap (LegendreBase p) (LegendreBraidRing p)))
    (V.map (algebraMap (LegendreBase p) (LegendreBraidRing p)))
    (U.map (algebraMap (LegendreBase p) (LegendreBraidRing p)))
    (Z.map (algebraMap (LegendreBase p) (LegendreBraidRing p))) A B C hC hB hA
  have ht' := congrArg (fun e => e.hom.left ≫
    coefficientScalarQuotientMorphism W (LegendreBraidRing p) p) ht
  simp only [Iso.trans_hom, Over.comp_left, Category.assoc] at ht'
  exact (composeThreeSquares _ _ _ _ f g h _ _ _ hf hg hh).trans ht'

omit [Fact p.Prime] in
theorem braidSwapCoordinate_map :
    (signCoordinateChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ))
      (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) 1)).map
      (quadraticTripleFirstMap (-1) (legendreParameterUnit p)
        (legendreComplementUnit p)).toRingHom =
        legendreSwapChange (legendreBraidMinusOneRoot p) := by
  ext <;> simp only [signCoordinateChange, legendreSwapChange, VariableChange.map,
    map_one, map_zero]
  rfl

omit [Fact p.Prime] in
theorem braidParameterCoordinate_map :
    (signCoordinateChange (quadraticEtaleUnit (legendreParameterUnit p))
      (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p) 0)).map
      (quadraticTripleSecondMap (-1) (legendreParameterUnit p)
        (legendreComplementUnit p)).toRingHom =
        legendreReciprocalChange (legendreBraidParameterRoot p) := by
  ext <;> simp only [signCoordinateChange, legendreReciprocalChange, VariableChange.map, map_zero]
  rfl

omit [Fact p.Prime] in
theorem braidComplementCoordinate_map :
    (signCoordinateChange (quadraticEtaleUnit (legendreComplementUnit p))
      (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreComplementUnit p)) 0)).map
      (quadraticTripleThirdMap (-1) (legendreParameterUnit p)
        (legendreComplementUnit p)).toRingHom =
        legendreReciprocalChange (legendreBraidComplementRoot p) := by
  ext <;> simp only [signCoordinateChange, legendreReciprocalChange, VariableChange.map, map_zero]
  rfl

/-- The two actual descended Legendre composites satisfy the mixed braid relation. -/
theorem legendreBraid_descended :
    legendreBraidLeftComposite p = legendreBraidRightComposite p := by
  let W := legendreModel p
  let V := legendreCurve (1 - legendreParameter p)
  let U := legendreCurve (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)
  let Z := legendreCurve (1 -
    (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
  let V' := legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)
  let U' := legendreCurve (1 -
    (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
  let σs := quadraticTripleFirstMap (-1 : (LegendreBase p)ˣ)
    (legendreParameterUnit p) (legendreComplementUnit p)
  let σr := quadraticTripleSecondMap (-1 : (LegendreBase p)ˣ)
    (legendreParameterUnit p) (legendreComplementUnit p)
  let σc := quadraticTripleThirdMap (-1 : (LegendreBase p)ˣ)
    (legendreParameterUnit p) (legendreComplementUnit p)
  have hs := quadraticCoordinateDesc_braid_fac p W (-1) V σs rfl rfl 1
    (legendreSwap_coordinate_equation p)
  have hl₁ := quadraticCoordinateDesc_braid_fac p V (legendreComplementUnit p) U σc rfl rfl 0
    (legendreBraidComplement_equation p)
  have hl₂ := quadraticCoordinateDesc_braid_fac p U (-1) Z σs rfl rfl 1
    (legendreBraidSwap_equation p _)
  have hr := quadraticCoordinateDesc_braid_fac p W (legendreParameterUnit p) V' σr rfl rfl 0
    (legendreReciprocal_coordinate_equation p)
  have hr₁ := quadraticCoordinateDesc_braid_fac p V' (-1) U' σs rfl rfl 1
    (legendreBraidSwap_equation p _)
  have hr₂ := quadraticCoordinateDesc_braid_fac p U' (legendreBraidLastUnit p) Z
    (legendreBraidLastMap p) rfl rfl 0 (legendreBraidRightLast_equation p)
  have hL := braidCyclic_transport_three p W V U Z _ _ _ _ _ _
    (legendreSwapDescendedMap p) (legendreBraidComplementDescendedMap p)
    (legendreBraidLeftLastMap p) hs hl₁ hl₂
  have hR := braidCyclic_transport_three p W V' U' Z _ _ _ _ _ _
    (legendreReciprocalDescendedMap p) (legendreBraidRightMiddleMap p)
    (legendreBraidRightLastMap p) hr hr₁ hr₂
  apply braidCyclic_hom_ext p Z
  apply hL.trans
  apply Eq.trans _ hR.symm
  apply congrArg (fun e :
      scalarQuotientModel (Z.map (algebraMap (LegendreBase p) (LegendreBraidRing p))) p ≅
        scalarQuotientModel (W.map (algebraMap (LegendreBase p) (LegendreBraidRing p))) p =>
      e.hom.left ≫ coefficientScalarQuotientMorphism W (LegendreBraidRing p) p)
  apply variableChangeCyclic_congr
  dsimp only [σs, σr, σc]
  simp only [braidSwapCoordinate_map, braidComplementCoordinate_map,
    legendreBraidLastMap_coordinate, braidParameterCoordinate_map]
  exact legendreBraidCover_coordinate_relation p

end WeierstrassCurve.CubicCharts

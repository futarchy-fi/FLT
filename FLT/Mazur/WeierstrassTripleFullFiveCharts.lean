/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionInputCharts
public import FLT.Mazur.WeierstrassFiveRegularSectionDescent

/-!
# Five regular chart presentations on every full triple-cover member

The first three points use the original tensor input charts of the inner
addition domains. The last two use their already constructed output charts.
All five Z coordinates are regular on every flat restriction of the member.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Choose one of the two actual inner-law indices on a full-cover member. -/
def tripleFullInnerIndex (i : (integralCurveTripleFullCover W hΔ).I₀)
    (b : Bool) : (integralCurveAdditionCover W hΔ).I₀ := if b then i.2.2 else i.2.1

/-- The actual projection to the chosen original inner-law domain. -/
def tripleFullInnerDomain (i : (integralCurveTripleFullCover W hΔ).I₀) (b : Bool) :
    (integralCurveTripleFullCover W hΔ).X i ⟶
      (integralCurveAdditionCover W hΔ).X (tripleFullInnerIndex W hΔ i b) := by
  cases b
  · exact integralCurveTripleFullInner W hΔ i ≫ integralCurveTripleInnerLeftDomain W hΔ i.2
  · exact integralCurveTripleFullInner W hΔ i ≫ integralCurveTripleInnerRightDomain W hΔ i.2

/-- Both inner-law projections are flat on every full-cover member. -/
instance tripleFullInnerDomain_flat (i : (integralCurveTripleFullCover W hΔ).I₀) (b : Bool) :
    Flat (tripleFullInnerDomain W hΔ i b) := by
  cases b
  · exact tripleFull_innerLeft_flat W hΔ i
  · exact tripleFull_innerRight_flat W hΔ i

/-- The chosen projection retains its actual original input pair. -/
theorem tripleFullInnerDomain_inputs (i : (integralCurveTripleFullCover W hΔ).I₀)
    (b : Bool) : tripleFullInnerDomain W hΔ i b ≫
        (integralCurveAdditionCover W hΔ).f (tripleFullInnerIndex W hΔ i b) =
      (integralCurveTripleFullCover W hΔ).f i ≫ tripleInnerPair W b := by
  cases b
  · change (_ ≫ _) ≫ (integralCurveAdditionCover W hΔ).f i.2.1 = _
    rw [Category.assoc, integralCurveTripleInnerLeftDomain_inputs, ← Category.assoc,
      integralCurveTripleFullInner_inputs]
    rfl
  · change (_ ≫ _) ≫ (integralCurveAdditionCover W hΔ).f i.2.2 = _
    rw [Category.assoc, integralCurveTripleInnerRightDomain_inputs, ← Category.assoc,
      integralCurveTripleFullInner_inputs]
    rfl

/-- Either input of either inner law is its original global triple input. -/
theorem tripleFullInnerDomain_input_global
    (i : (integralCurveTripleFullCover W hΔ).I₀) (b c : Bool) :
    (tripleFullInnerDomain W hΔ i b ≫
      integralCurveAdditionInputSpec W hΔ (tripleFullInnerIndex W hΔ i b) c) ≫
        integralCurveChart W (productChartCoordinate (integralCurveAdditionInputChart W hΔ
          (tripleFullInnerIndex W hΔ i b) c)) =
      (integralCurveTripleFullCover W hΔ).f i ≫
        tripleInnerPair W b ≫ integralCurveProductProjection W c := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => tripleFullInnerDomain W hΔ i b ≫ g)
      (integralCurveAdditionInputSpec_global W hΔ (tripleFullInnerIndex W hΔ i b) c)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun g => g ≫ integralCurveProductProjection W c)
            (tripleFullInnerDomain_inputs W hΔ i b)).trans (Category.assoc _ _ _))))

/-- The five chart indices for the actual inputs and intermediate sums. -/
def tripleFullFiveChart (i : (integralCurveTripleFullCover W hΔ).I₀) : Fin 5 → Fin 3 :=
  ![productChartCoordinate (integralCurveAdditionInputChart W hΔ i.2.1 false),
    productChartCoordinate (integralCurveAdditionInputChart W hΔ i.2.1 true),
    productChartCoordinate (integralCurveAdditionInputChart W hΔ i.2.2 true),
    integralCurveAdditionOutput W hΔ i.2.1, integralCurveAdditionOutput W hΔ i.2.2]

/-- Chart presentations of the five actual points on a full-cover member. -/
def tripleFullFiveSpec (i : (integralCurveTripleFullCover W hΔ).I₀) (n : Fin 5) :
    (integralCurveTripleFullCover W hΔ).X i ⟶ chartScheme W (tripleFullFiveChart W hΔ i n) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (fun x => Fin.elim0 x))))) n
  · exact tripleFullInnerDomain W hΔ i false ≫ integralCurveAdditionInputSpec W hΔ i.2.1 false
  · exact tripleFullInnerDomain W hΔ i false ≫ integralCurveAdditionInputSpec W hΔ i.2.1 true
  · exact tripleFullInnerDomain W hΔ i true ≫ integralCurveAdditionInputSpec W hΔ i.2.2 true
  · exact tripleFullInnerDomain W hΔ i false ≫ integralCurveAdditionSpec W hΔ i.2.1
  · exact tripleFullInnerDomain W hΔ i true ≫ integralCurveAdditionSpec W hΔ i.2.2

/-- The five presentations retain exactly the three inputs and the two inner sums. -/
theorem tripleFullFiveSpec_global (i : (integralCurveTripleFullCover W hΔ).I₀) (n : Fin 5) :
    tripleFullFiveSpec W hΔ i n ≫ integralCurveChart W (tripleFullFiveChart W hΔ i n) =
      tripleFivePoint W hΔ ((integralCurveTripleFullCover W hΔ).f i) n := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (fun x => Fin.elim0 x))))) n
  · exact tripleFullInnerDomain_input_global W hΔ i false false
  · exact tripleFullInnerDomain_input_global W hΔ i false true
  · exact (tripleFullInnerDomain_input_global W hΔ i true true).trans
      (congrArg (fun f => (integralCurveTripleFullCover W hΔ).f i ≫ f)
        (integralCurveTripleLastPair_snd W))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => tripleFullInnerDomain W hΔ i false ≫ f)
        (integralCurveAdditionSpec_local W hΔ i.2.1)).trans
          ((Category.assoc _ _ _).trans (integralCurveTripleFull_innerLeft W hΔ i).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => tripleFullInnerDomain W hΔ i true ≫ f)
        (integralCurveAdditionSpec_local W hΔ i.2.2)).trans
          ((Category.assoc _ _ _).trans (integralCurveTripleFull_innerRight W hΔ i).symm))

/-- All five coordinates remain regular on an arbitrary flat restriction of a full member. -/
theorem tripleFullFiveSpec_z_regular (i : (integralCurveTripleFullCover W hΔ).I₀)
    {X : Scheme.{u}} (f : X ⟶ (integralCurveTripleFullCover W hΔ).X i) [Flat f] (n : Fin 5) :
    IsRegular (specSectionHom (f ≫ tripleFullFiveSpec W hΔ i n)
      (coord W (tripleFullFiveChart W hΔ i n) 2)) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (fun x => Fin.elim0 x))))) n
  · change IsRegular (specSectionHom (f ≫ tripleFullInnerDomain W hΔ i false ≫ _) _)
    rw [← Category.assoc]
    exact integralCurveAdditionInputSpec_z_regular W hΔ i.2.1 false
      (f ≫ tripleFullInnerDomain W hΔ i false)
  · change IsRegular (specSectionHom (f ≫ tripleFullInnerDomain W hΔ i false ≫ _) _)
    rw [← Category.assoc]
    exact integralCurveAdditionInputSpec_z_regular W hΔ i.2.1 true
      (f ≫ tripleFullInnerDomain W hΔ i false)
  · change IsRegular (specSectionHom (f ≫ tripleFullInnerDomain W hΔ i true ≫ _) _)
    rw [← Category.assoc]
    exact integralCurveAdditionInputSpec_z_regular W hΔ i.2.2 true
      (f ≫ tripleFullInnerDomain W hΔ i true)
  · change IsRegular (specSectionHom (f ≫ tripleFullInnerDomain W hΔ i false ≫ _) _)
    rw [← Category.assoc]
    exact integralCurveAdditionSpec_z_regular W hΔ i.2.1
      (f ≫ tripleFullInnerDomain W hΔ i false)
  · change IsRegular (specSectionHom (f ≫ tripleFullInnerDomain W hΔ i true ≫ _) _)
    rw [← Category.assoc]
    exact integralCurveAdditionSpec_z_regular W hΔ i.2.2
      (f ≫ tripleFullInnerDomain W hΔ i true)

end FLT.Mazur.WeierstrassIntegralChart

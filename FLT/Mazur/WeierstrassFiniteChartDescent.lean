/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveProduct

/-!
# Simultaneous Y/Z chart descent for finite families of curve morphisms

Successive pullbacks of the actual two-chart atlas give simultaneous chart
presentations of any finite family. Every resulting restriction is an open
immersion, so flatness of a source morphism survives this descent.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Equality descends from simultaneous Y/Z presentations of finitely many actual points. -/
theorem finiteCurveCharts_hom_ext (n : ℕ) {X Y : Scheme.{u}}
    (q : Fin n → (X ⟶ integralCurve W)) (f g : X ⟶ Y)
    (h : ∀ (Z : Scheme.{u}) (a : Z ⟶ X), IsOpenImmersion a →
      ∀ (b : Fin n → Bool) (p : (i : Fin n) → Z ⟶ chartScheme W (productChartCoordinate (b i))),
      (∀ i, p i ≫ integralCurveChart W (productChartCoordinate (b i)) = a ≫ q i) →
      a ≫ f = a ≫ g) : f = g := by
  induction n generalizing X with
  | zero =>
    simpa only [Category.id_comp] using
      h X (𝟙 X) inferInstance (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  | succ n ih =>
    let C := integralCurveTwoChartCover W
    apply Scheme.Cover.hom_ext (C.pullback₁ (q 0))
    intro i
    let a := (C.pullback₁ (q 0)).f i
    let p₀ := Scheme.Cover.pullbackHom C (q 0) i
    have hp₀ : p₀ ≫ integralCurveChart W (productChartCoordinate i) = a ≫ q 0 :=
      Scheme.Cover.pullbackHom_map C (q 0) i
    apply ih (fun j => a ≫ q j.succ) (a ≫ f) (a ≫ g)
    intro Z v hv b p hp
    let _ := hv
    let b' : Fin (n + 1) → Bool := Fin.cases i b
    let p' : (j : Fin (n + 1)) → Z ⟶ chartScheme W (productChartCoordinate (b' j)) :=
      Fin.cases (v ≫ p₀) p
    have he : ∀ j, p' j ≫ integralCurveChart W (productChartCoordinate (b' j)) =
        (v ≫ a) ≫ q j := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact (Category.assoc _ _ _).trans
          ((congrArg (fun z => v ≫ z) hp₀).trans (Category.assoc _ _ _).symm)
      · exact (hp k).trans (Category.assoc _ _ _).symm
    simpa only [Category.assoc] using h Z (v ≫ a) inferInstance b' p' he

end FLT.Mazur.WeierstrassIntegralChart

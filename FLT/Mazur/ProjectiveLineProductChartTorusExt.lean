/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineProductTorusExt

/-!
# Either punctured product chart determines a separated morphism

Inverting the overlap coordinate carries the right-chart puncture to the
left-chart puncture. Thus either chart suffices for the same density test.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLineProductCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K S : Type u) [Field K] [CommRing S] [IsDomain S] [Algebra K S]

/-- Either original chart's torus detects maps from the complete projective-line product. -/
theorem product_hom_ext_chart_overlap {Y B : Scheme.{u}} (p : Y ⟶ B) [IsSeparated p]
    (f g : product K S ⟶ Y) (hb : f ≫ p = g ≫ p) (b : Bool)
    (h : ProjectiveLineProductOverlap.left S ≫ productChartMap K S b ≫ f =
      ProjectiveLineProductOverlap.left S ≫ productChartMap K S b ≫ g) : f = g := by
  cases b with
  | false => exact product_hom_ext_overlap K S p f g hb h
  | true =>
    apply product_hom_ext_overlap K S p f g hb
    have he := congrArg ((ProjectiveLineProductOverlap.inversion S).hom ≫ ·) h
    change ProjectiveLineProductOverlap.right S ≫ productChartMap K S true ≫ f =
      ProjectiveLineProductOverlap.right S ≫ productChartMap K S true ≫ g at he
    simpa only [← Category.assoc, ← ProjectiveLineProductOverlap.condition] using he

end FLT.Mazur.ProjectiveLineProductCharts

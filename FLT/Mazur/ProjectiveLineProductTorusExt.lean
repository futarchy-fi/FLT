/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineProductOverlap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The Laurent overlap detects maps from a parameterized projective line

Over a domain parameter ring, the puncture is dense in each reduced polynomial
chart. Agreement there determines maps to any separated relative target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.ProjectiveLineProductCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K S : Type u) [Field K] [CommRing S] [IsDomain S] [Algebra K S]

/-- The puncture remains dominant over every domain parameter ring. -/
instance productOverlapLeft_dominant : IsDominant (ProjectiveLineProductOverlap.left S) := by
  let f := ProjectiveLineProductOverlap.left S
  exact ⟨f.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩

/-- The reciprocal puncture also detects the second polynomial chart. -/
instance productOverlapRight_dominant : IsDominant (ProjectiveLineProductOverlap.right S) := by
  let f := ProjectiveLineProductOverlap.right S
  exact ⟨f.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩

/-- The single Laurent overlap detects the entire product morphism to a separated target. -/
theorem product_hom_ext_overlap {Y B : Scheme.{u}} (p : Y ⟶ B) [IsSeparated p]
    (f g : product K S ⟶ Y) (hb : f ≫ p = g ≫ p)
    (h : ProjectiveLineProductOverlap.left S ≫ productChartMap K S false ≫ f =
      ProjectiveLineProductOverlap.left S ≫ productChartMap K S false ≫ g) : f = g := by
  apply (ProjectiveLineProductOverlap.isPushout K S).hom_ext
  · apply ext_of_isDominant_of_isSeparated p
      (by simpa only [Category.assoc] using congrArg (productChartMap K S false ≫ ·) hb)
      (ProjectiveLineProductOverlap.left S)
    exact h
  · apply ext_of_isDominant_of_isSeparated p
      (by simpa only [Category.assoc] using congrArg (productChartMap K S true ≫ ·) hb)
      (ProjectiveLineProductOverlap.right S)
    simpa only [← Category.assoc, ← ProjectiveLineProductOverlap.condition] using h

end FLT.Mazur.ProjectiveLineProductCharts

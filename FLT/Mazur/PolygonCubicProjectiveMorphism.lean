/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicProjectiveCharts
public import FLT.Mazur.ModuleSectionProjectiveGluing

/-!
# The projective morphism of the actual polygon cubic family

The full finite interpolation family, including the proved generating pair,
now gives a global morphism to projective space. Its restriction to every
nonvanishing open is the previously constructed chart morphism. No closed
immersion or hyperplane pullback identification is assumed here.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The finite cubic family defines a genuine global projective-space morphism. -/
def cubicProjectiveMorphism : C.left ⟶ ProjectiveSpace.space K (Fin (n * 3 + 1 + 1)) :=
  sectionProjectiveMorphism (polygonLine K n hn p q h a 3) (n * 3 + 1)
    (finiteCubicFamily K n hn p q h a) (iSup_finiteCubicOpen K n hn p q h a)
      (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)

/-- The glued map is the actual ratio morphism on each denominator's nonvanishing open. -/
@[reassoc] lemma finiteCubicOpen_ι_projectiveMorphism (i : Fin (n * 3 + 1 + 1)) :
    (finiteCubicOpen K n hn p q h a i).ι ≫ cubicProjectiveMorphism K n hn p q h a =
      cubicProjectiveChartMorphism K n hn p q h a i :=
  sectionGeneratorOpen_ι_projectiveMorphism (polygonLine K n hn p q h a 3) (n * 3 + 1)
    (finiteCubicFamily K n hn p q h a) (iSup_finiteCubicOpen K n hn p q h a)
      (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) i

/-- The two actual local morphisms agree on every intersection of denominator opens. -/
lemma cubicProjectiveChartMorphism_overlap (i j : Fin (n * 3 + 1 + 1)) :
    C.left.homOfLE (show finiteCubicOpen K n hn p q h a i ⊓
      finiteCubicOpen K n hn p q h a j ≤ finiteCubicOpen K n hn p q h a i
        from inf_le_left) ≫ cubicProjectiveChartMorphism K n hn p q h a i =
      C.left.homOfLE inf_le_right ≫ cubicProjectiveChartMorphism K n hn p q h a j :=
  sectionProjectiveLocalMorphism_inf (polygonLine K n hn p q h a 3) (n * 3 + 1)
    (finiteCubicFamily K n hn p q h a)
      (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) i j

/-- The global cubic morphism pulls standard charts back to the actual denominator opens. -/
lemma cubicProjectiveMorphism_preimage_chart (i : Fin (n * 3 + 1 + 1)) :
    cubicProjectiveMorphism K n hn p q h a ⁻¹ᵁ
      ProjectiveSpace.chart K (Fin (n * 3 + 1 + 1)) i = finiteCubicOpen K n hn p q h a i :=
  sectionProjectiveMorphism_preimage_chart (polygonLine K n hn p q h a 3) (n * 3 + 1)
    (finiteCubicFamily K n hn p q h a) (iSup_finiteCubicOpen K n hn p q h a)
      (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) i

end FLT.Mazur.PolygonCubicSections

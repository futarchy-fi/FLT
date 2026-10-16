/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalMarkingEquations
public import FLT.Mazur.CartierPullbackParameterRegular

/-!
# Regular equations for the actual marking on whole arithmetic charts

The full global Cartier ideal has an explicit principal equation on each node
chart. Its original equation is regular over every nilpotent coefficient base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n) (i j : Fin n) (a : Rˣ)
local notation "J" => Scheme.IdealSheafData.comap
  (Scheme.Hom.ker (marking R t n h i a)) (chart R t n h j)
local notation "e" => CommRingCat.Hom.hom
  (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of (ChartRing t))))

include h in
/-- The specified equation is regular in the full arithmetic chart's section ring. -/
theorem marking_chart_section_regular :
    IsRegular (e (chartMarkingEquation R t n i j a)) := by
  let _ : IsAffine (PolygonSmoothing.chart R t) :=
    inferInstanceAs (IsAffine (Spec (.of (ChartRing t))))
  have hc : EffectiveCartier (J) :=
    (marking_cartier R t n h i a).1.comap_of_isOpenImmersion (chart R t n h j)
  have hi : EffectiveCartier ((J).comap (𝟙 _)) := by
    simpa only [Scheme.IdealSheafData.comap_id] using hc
  have hr := cartierPullbackParameter_regular (𝟙 _) (J)
    (e (chartMarkingEquation R t n i j a))
    (marking_ideal_chart_sections R t n h i j a) hi
  simpa using hr

include h in
/-- The same original ring equation is a non-zero-divisor, without reducing the base. -/
theorem chartMarkingEquation_regular : IsRegular (chartMarkingEquation R t n i j a) := by
  have he := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (ChartRing t))).inv).injective
  have hr := marking_chart_section_regular R t n h i j a
  constructor
  · intro b c hb
    apply he
    apply hr.left
    simpa only [map_mul] using congrArg e hb
  · intro b c hb
    apply he
    apply hr.right
    simpa only [map_mul] using congrArg e hb

/-- Each whole arithmetic node chart is a Cartier chart for the actual pulled marking. -/
theorem marking_cartier_whole_chart :
    CartierChart (J) ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩ :=
  ⟨e (chartMarkingEquation R t n i j a), marking_chart_section_regular R t n h i j a,
    marking_ideal_chart_sections R t n h i j a⟩

/-- Its actual image in the glued family is a Cartier chart for the original global ideal. -/
theorem marking_cartier_chart_image :
    CartierChart (marking R t n h i a).ker
      ⟨chart R t n h j ''ᵁ ⊤,
        (isAffineOpen_top (Spec (.of (ChartRing t)))).image_of_isOpenImmersion _⟩ :=
  (cartierChart_comap_iff _ _ _).mp (marking_cartier_whole_chart R t n h i j a)

end FLT.Mazur.PolygonInfinitesimal

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalChartMarkingIdeals
public import FLT.Mazur.PolygonDivisorPowerPullback

/-!
# Exact equations for every power of the original arithmetic marking

The chart equation is x-a at the labeled outgoing chart, y-a⁻¹ at the
preceding chart, and one elsewhere. Ideal powers keep their full multiplicity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (R : Type u) [CommRing R] (t : R)
  (n : ℕ) (h : 2 ≤ n) (i j : Fin n) (a : Rˣ)

/-- The original global marking's specified equation on an arithmetic node chart. -/
def chartMarkingEquation : ChartRing t :=
  if j = i then leftCoordinate t - algebraMap R (ChartRing t) (a : R)
  else if j = (finRotate n).symm i then
    rightCoordinate t - algebraMap R (ChartRing t) (a⁻¹ : Rˣ)
  else 1

variable [Fact (IsNilpotent t)]

/-- The full pulled global ideal has this exact principal equation in the original ring. -/
theorem marking_ideal_chart_coordinate :
    (((marking R t n h i a).ker.comap (chart R t n h j)).ideal
      ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩).comap
        (Scheme.ΓSpecIso (.of (ChartRing t))).inv.hom =
          Ideal.span {chartMarkingEquation R t n i j a} := by
  by_cases hji : j = i
  · subst j
    rw [marking_ideal_own_chart, markedSection_ideal_coordinate]
    simp only [chartMarkingEquation, ite_true, markedCoordinateIdeal]
  · by_cases hjp : j = (finRotate n).symm i
    · subst j
      rw [marking_ideal_preceding_chart, incomingMarkedSection_ideal_coordinate]
      simp only [chartMarkingEquation, ite_eq_right hji, ite_true]
    · rw [marking_ideal_other_chart R t n h i a hji hjp]
      simp only [chartMarkingEquation, ite_eq_right hji, ite_eq_right hjp,
        Scheme.IdealSheafData.ideal_top, Pi.top_apply, Ideal.comap_top, Ideal.span_singleton_one]

/-- The same equation describes the section ideal in the scheme's section ring. -/
theorem marking_ideal_chart_sections :
    ((marking R t n h i a).ker.comap (chart R t n h j)).ideal
      ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩ =
        Ideal.span {((Scheme.ΓSpecIso (.of (ChartRing t))).inv.hom
          (chartMarkingEquation R t n i j a))} := by
  have he := congrArg (Ideal.map (Scheme.ΓSpecIso (.of (ChartRing t))).inv.hom)
    (marking_ideal_chart_coordinate R t n h i j a)
  rw [Ideal.map_comap_of_surjective (Scheme.ΓSpecIso (.of (ChartRing t))).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ChartRing t))).inv).surjective,
    Ideal.map_span, Set.image_singleton] at he
  exact he

/-- Every original ideal power keeps its exact multiplicity in the full chart ring. -/
theorem marking_power_chart_coordinate (d : ℕ) :
    ((((marking R t n h i a).ker ^ d).comap (chart R t n h j)).ideal
      ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩).comap
        (Scheme.ΓSpecIso (.of (ChartRing t))).inv.hom =
          Ideal.span {chartMarkingEquation R t n i j a ^ d} := by
  rw [FCurve.idealSheaf_comap_pow]
  let e := (Scheme.ΓSpecIso (.of (ChartRing t))).commRingCatIsoToRingEquiv
  let I := ((marking R t n h i a).ker.comap (chart R t n h j)).ideal
    ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩
  have hc : Ideal.map e.toRingHom I = Ideal.span {chartMarkingEquation R t n i j a} :=
    (Ideal.map_comap_of_equiv e).trans (marking_ideal_chart_coordinate R t n h i j a)
  change Ideal.comap e.symm.toRingHom (I ^ d) = _
  calc
    _ = Ideal.map e.toRingHom (I ^ d) := (Ideal.map_comap_of_equiv e).symm
    _ = Ideal.map e.toRingHom I ^ d := Ideal.map_pow _ _ _
    _ = Ideal.span {chartMarkingEquation R t n i j a} ^ d := congrArg (fun J ↦ J ^ d) hc
    _ = _ := Ideal.span_singleton_pow _ _

end FLT.Mazur.PolygonInfinitesimal

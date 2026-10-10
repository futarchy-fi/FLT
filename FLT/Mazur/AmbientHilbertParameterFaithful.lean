/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertChartParameterEquality

/-!
# Faithfulness of the global full universal Hilbert family

Two arbitrary parameters with equal full universal pullbacks agree. Pulling
back the chart cover twice reduces this to the proved cross-chart uniqueness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- A chart factorization computes the full global universal pullback. -/
theorem parameterFamily_of_chart_factor (p : A.GluedParameters d s) (i : A.Index)
    (q : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s)
    (h : q.val ≫ A.hilbertChart d i = p.val) :
    A.parameterFamily d s p = A.chartParameterFamily d s i q := by
  have he : A.chartParameter d s i q = p := Subtype.ext h
  rw [← he, A.parameterFamily_chart]

/-- Arbitrary parameters are determined by their full universal ideal family. -/
theorem parameterFamily_injective : Function.Injective (A.parameterFamily d s) := by
  intro p q h
  apply Subtype.ext
  let H := A.hilbertOpenCover d
  let C := H.pullback₁ p.val
  apply Scheme.Cover.hom_ext C
  intro i
  let D := H.pullback₁ (C.f i ≫ q.val)
  apply Scheme.Cover.hom_ext D
  intro j
  let u := D.f j ≫ C.f i
  let t := u ≫ s
  let a := D.f j ≫ H.pullbackHom p.val i
  let b := H.pullbackHom (C.f i ≫ q.val) j
  have ha : a ≫ A.hilbertChart d i = u ≫ p.val := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (D.f j ≫ ·) (H.pullbackHom_map p.val i)).trans
        (Category.assoc _ _ _).symm)
  have hb : b ≫ A.hilbertChart d j = u ≫ q.val := by
    exact (H.pullbackHom_map (C.f i ≫ q.val) j).trans (Category.assoc _ _ _).symm
  let pa : AmbientSchemeParameters R (A.Vars i) d (A.relations i) t := ⟨a, by
    change a ≫ A.chartBase d i = t
    rw [← A.hilbertChart_over d i, ← Category.assoc, ha, Category.assoc, p.property]⟩
  let qb : AmbientSchemeParameters R (A.Vars j) d (A.relations j) t := ⟨b, by
    change b ≫ A.chartBase d j = t
    rw [← A.hilbertChart_over d j, ← Category.assoc, hb, Category.assoc, q.property]⟩
  have he := congrArg (relativeIdealFamilyBaseChange z d s t u rfl) h
  rw [A.parameterFamily_natural, A.parameterFamily_natural] at he
  rw [A.parameterFamily_of_chart_factor d t _ i pa ha,
    A.parameterFamily_of_chart_factor d t _ j qb hb] at he
  have he' := congrArg Subtype.val (A.chartParameter_eq_of_family_eq d t i j pa qb he)
  change a ≫ A.hilbertChart d i = b ≫ A.hilbertChart d j at he'
  rw [ha, hb] at he'
  simpa only [u, Category.assoc] using he'

end FLT.Mazur.HilbertChart.AmbientQuotientCharts

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertParameterFaithful
public import FLT.Mazur.AmbientHilbertSupportedClassification
public import FLT.Mazur.RelativeIdealFamilySupportOpen

/-!
# Exact images of the original ambient Hilbert charts

An arbitrary parameter enters an original chart exactly when its full family
is supported there. Consequently the chart image is the exact support open
of the global universal family, as an equality of original scheme opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover
namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
  (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
  {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) (i : A.Index)

/-- Entry into a glued Hilbert chart is equivalent to support of the entire original family. -/
theorem parameter_range_chart_iff (p : A.GluedParameters d s) :
    Set.range p.val ⊆ (A.hilbertChart d i).opensRange ↔
      Set.range ((A.parameterFamily d s p).val.subschemeι ≫ pullback.snd s z) ⊆
        (A.chart i).opensRange := by
  constructor
  · intro h
    let q := IsOpenImmersion.lift (A.hilbertChart d i) p.val h
    have hq : q ≫ A.hilbertChart d i = p.val := IsOpenImmersion.lift_fac _ _ _
    let b : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s := ⟨q, by
      change q ≫ A.chartBase d i = s
      rw [← A.hilbertChart_over d i, ← Category.assoc, hq, p.property]⟩
    rw [A.parameterFamily_of_chart_factor d s p i b hq]
    exact A.chartParameterFamily_originalSupport d s i b
  · intro h
    have hs : Set.range (A.parameterFamily d s p).val.subschemeι ⊆ Set.range
        (relativeIdealAmbientHom (A.originalChartBase i) z (A.chart i)
          (A.chart_over i) s) := by
      rw [relativeIdealAmbientHom_range]
      rintro _ ⟨y, rfl⟩
      exact h ⟨y, rfl⟩
    let q := A.supportedParameter d s i (A.parameterFamily d s p) hs
    have he : A.chartParameter d s i q = p :=
      A.parameterFamily_injective d s
        (A.parameterFamily_supportedParameter d s i (A.parameterFamily d s p) hs)
    rw [← he]
    rintro _ ⟨x, rfl⟩
    exact ⟨q.val x, rfl⟩

/-- The universal full-family support locus for one original affine ambient. -/
def chartSupportLocus (i : A.Index) : (A.gluedHilbert d).Opens :=
  relativeIdealFamilySupportOpen z d (A.gluedBase d) (A.universalFamily d)
    (A.chart i).opensRange

/-- The support locus detects exactly the same original parameters as the chart image. -/
theorem parameter_range_support_iff (p : A.GluedParameters d s) :
    Set.range p.val ⊆ A.chartSupportLocus d i ↔
      Set.range p.val ⊆ (A.hilbertChart d i).opensRange := by
  rw [A.parameter_range_chart_iff]
  exact relativeIdealFamilySupportOpen_factorization z d (A.gluedBase d)
    (A.universalFamily d) (A.chart i).opensRange s p.val p.property

/-- Original chart images are precisely the support opens of the actual universal family. -/
theorem chartSupportLocus_eq : A.chartSupportLocus d i = (A.hilbertChart d i).opensRange := by
  apply le_antisymm
  · let U := A.chartSupportLocus d i
    have h := (A.parameter_range_support_iff d (U.ι ≫ A.gluedBase d) i ⟨U.ι, rfl⟩).mp
      (by rw [Scheme.Opens.range_ι])
    rwa [Scheme.Opens.range_ι] at h
  · have h := (A.parameter_range_support_iff d (A.chartBase d i) i
      ⟨A.hilbertChart d i, A.hilbertChart_over d i⟩).mpr (Set.Subset.refl _)
    exact h

end FLT.Mazur.HilbertChart.AmbientQuotientCharts

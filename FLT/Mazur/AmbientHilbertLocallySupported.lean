/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertSupportedCoverGluing

/-!
# The exact full-family image of the glued Hilbert scheme

The constructed scheme represents precisely full finite locally free families
that locally lie in one original affine chart. Both inverse laws are proved;
existence of such neighborhoods for all families is a separate geometric task.
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

/-- The full family's support locally lies in one original affine ambient chart. -/
def LocallySupportedFamily (J : RelativeIdealFamilies z d s) : Prop :=
  ∃ (C : X.OpenCover.{u}) (k : C.I₀ → A.Index), ∀ i, Set.range
    (relativeIdealFamilyBaseChange z d s (C.f i ≫ s) (C.f i) rfl J).val.subschemeι ⊆
      Set.range (relativeIdealAmbientHom (A.originalChartBase (k i)) z
        (A.chart (k i)) (A.chart_over (k i)) (C.f i ≫ s))

/-- Every actual universal pullback has local original affine support. -/
theorem parameterFamily_locallySupported (p : A.GluedParameters d s) :
    A.LocallySupportedFamily d s (A.parameterFamily d s p) := by
  let H := A.hilbertOpenCover d
  let C := H.pullback₁ p.val
  refine ⟨C, fun i ↦ i, fun i ↦ ?_⟩
  let q : AmbientSchemeParameters R (A.Vars i) d (A.relations i) (C.f i ≫ s) :=
    ⟨H.pullbackHom p.val i, by
      change H.pullbackHom p.val i ≫ A.chartBase d i = C.f i ≫ s
      rw [← A.hilbertChart_over d i, ← Category.assoc]
      exact (congrArg (· ≫ A.gluedBase d) (H.pullbackHom_map p.val i)).trans
        ((Category.assoc _ _ _).trans (congrArg (C.f i ≫ ·) p.property))⟩
  rw [A.parameterFamily_natural]
  let r : A.GluedParameters d (C.f i ≫ s) :=
    ⟨C.f i ≫ p.val, by rw [Category.assoc, p.property]⟩
  have hr : q.val ≫ A.hilbertChart d i = r.val := H.pullbackHom_map p.val i
  change Set.range (A.parameterFamily d (C.f i ≫ s) r).val.subschemeι ⊆ _
  rw [A.parameterFamily_of_chart_factor d (C.f i ≫ s) r i q hr]
  exact relativeIdealFamilyExtension_support _ _ _ _ _ _ _

/-- Local affine support is exactly membership in the full universal-pullback image. -/
theorem locallySupportedFamily_iff (J : RelativeIdealFamilies z d s) :
    A.LocallySupportedFamily d s J ↔ ∃ p, A.parameterFamily d s p = J := by
  constructor
  · rintro ⟨C, k, hJ⟩
    exact ⟨A.supportedCoverParameter d s J C k hJ,
      A.parameterFamily_supportedCoverParameter d s J C k hJ⟩
  · rintro ⟨p, rfl⟩
    exact A.parameterFamily_locallySupported d s p

/-- The unique actual classifying parameter of a locally supported full family. -/
def locallySupportedParameter (J : RelativeIdealFamilies z d s)
    (hJ : A.LocallySupportedFamily d s J) : A.GluedParameters d s :=
  ((A.locallySupportedFamily_iff d s J).mp hJ).choose

/-- The classifying parameter recovers the entire original ideal. -/
theorem parameterFamily_locallySupportedParameter (J : RelativeIdealFamilies z d s)
    (hJ : A.LocallySupportedFamily d s J) :
    A.parameterFamily d s (A.locallySupportedParameter d s J hJ) = J :=
  ((A.locallySupportedFamily_iff d s J).mp hJ).choose_spec

/-- Actual representation of all and only locally supported full ideal families. -/
def locallySupportedClassification :
    A.GluedParameters d s ≃
      { J : RelativeIdealFamilies z d s // A.LocallySupportedFamily d s J } where
  toFun p := ⟨A.parameterFamily d s p, A.parameterFamily_locallySupported d s p⟩
  invFun J := A.locallySupportedParameter d s J.val J.property
  left_inv _ := A.parameterFamily_injective d s
    (A.parameterFamily_locallySupportedParameter d s _ _)
  right_inv J := Subtype.ext (A.parameterFamily_locallySupportedParameter d s J.val J.property)

end FLT.Mazur.HilbertChart.AmbientQuotientCharts

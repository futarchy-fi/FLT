/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertLocalParameters
public import FLT.Mazur.RelativeIdealFamilyCover

/-!
# Global classification from actual local affine support

Local parameters constructed from full supported ideal families glue to an
actual global morphism. Its universal pullback recovers the entire input
family, and faithfulness proves uniqueness independent of the chosen cover.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) (J : RelativeIdealFamilies z d s)
variable (C : X.OpenCover.{u}) (k : C.I₀ → A.Index)
variable (hJ : ∀ i, Set.range
  (relativeIdealFamilyBaseChange z d s (C.f i ≫ s) (C.f i) rfl J).val.subschemeι ⊆
    Set.range (relativeIdealAmbientHom (A.originalChartBase (k i)) z
      (A.chart (k i)) (A.chart_over (k i)) (C.f i ≫ s)))

/-- Glue the constructed local supported parameters as actual scheme morphisms. -/
def supportedCoverMorphism : X ⟶ A.gluedHilbert d :=
  C.glueMorphisms (fun i ↦ (A.localSupportedParameter d s J C k hJ i).val)
    (A.localSupportedParameter_overlap d s J C k hJ)

/-- The global classifying morphism retains every constructed local parameter. -/
@[reassoc]
theorem supportedCoverMorphism_restrict (i : C.I₀) :
    C.f i ≫ A.supportedCoverMorphism d s J C k hJ =
      (A.localSupportedParameter d s J C k hJ i).val := C.ι_glueMorphisms _ _ i

/-- The glued classifying morphism lies over the original coefficient base. -/
theorem supportedCoverMorphism_over :
    A.supportedCoverMorphism d s J C k hJ ≫ A.gluedBase d = s := by
  apply C.hom_ext
  intro i
  rw [← Category.assoc, A.supportedCoverMorphism_restrict]
  exact (A.localSupportedParameter d s J C k hJ i).property

/-- The actual global parameter constructed from local affine support of the full family. -/
def supportedCoverParameter : A.GluedParameters d s :=
  ⟨A.supportedCoverMorphism d s J C k hJ, A.supportedCoverMorphism_over d s J C k hJ⟩

/-- Global universal pullback recovers the full input ideal from its local affine support. -/
theorem parameterFamily_supportedCoverParameter :
    A.parameterFamily d s (A.supportedCoverParameter d s J C k hJ) = J := by
  apply relativeIdealFamily_ext_openCover z s C d
  intro i
  rw [A.parameterFamily_natural]
  have h : (⟨C.f i ≫ (A.supportedCoverParameter d s J C k hJ).val, by
      rw [Category.assoc, (A.supportedCoverParameter d s J C k hJ).property]⟩ :
      A.GluedParameters d (C.f i ≫ s)) = A.localSupportedParameter d s J C k hJ i :=
    Subtype.ext (A.supportedCoverMorphism_restrict d s J C k hJ i)
  rw [h]
  exact A.localSupportedParameter_family d s J C k hJ i

include hJ in
/-- A full family with local affine support has exactly one actual global Hilbert parameter. -/
theorem existsUnique_parameter_of_supportedCover :
    ∃! p : A.GluedParameters d s, A.parameterFamily d s p = J := by
  refine ⟨A.supportedCoverParameter d s J C k hJ,
    A.parameterFamily_supportedCoverParameter d s J C k hJ, fun p hp ↦ ?_⟩
  exact A.parameterFamily_injective d s
    (hp.trans (A.parameterFamily_supportedCoverParameter d s J C k hJ).symm)

end FLT.Mazur.HilbertChart.AmbientQuotientCharts

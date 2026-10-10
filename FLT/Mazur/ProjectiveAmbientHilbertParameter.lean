/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveAmbientHilbertClassification

/-!
# Natural classifying morphisms for full projective families

Invert the proved classification to obtain the unique parameter. Recovery,
uniqueness, and arbitrary base-change naturality concern entire ideal
families and actual scheme morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
variable {B : Type u} [CommRing B] {ι : Type u}
variable (e : Z ⟶ ProjectiveSpace.space B ι) [IsClosedImmersion e] [IsSeparated z]
variable (d : ℕ) {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- The unique classifying parameter of an arbitrary full finite locally free ideal family. -/
def projectiveAmbientParameter (J : RelativeIdealFamilies z d s) :
    (allAffineAmbientCharts z).GluedParameters d s :=
  (projectiveAmbientClassification z e d s).symm J

/-- Universal pullback recovers the entire original family. -/
theorem projectiveAmbientParameter_family (J : RelativeIdealFamilies z d s) :
    (allAffineAmbientCharts z).parameterFamily d s (projectiveAmbientParameter z e d s J) = J :=
  (projectiveAmbientClassification z e d s).apply_symm_apply J

/-- Classifying the universal pullback recovers its original parameter. -/
theorem projectiveAmbientParameter_parameter
    (p : (allAffineAmbientCharts z).GluedParameters d s) :
    projectiveAmbientParameter z e d s ((allAffineAmbientCharts z).parameterFamily d s p) = p :=
  (projectiveAmbientClassification z e d s).symm_apply_apply p

/-- The classifying morphism commutes with arbitrary changes of the test scheme. -/
theorem projectiveAmbientParameter_natural (t : Y ⟶ Spec (.of R)) (g : Y ⟶ X)
    (hg : g ≫ s = t) (J : RelativeIdealFamilies z d s) :
    projectiveAmbientParameter z e d t (relativeIdealFamilyBaseChange z d s t g hg J) =
      ⟨g ≫ (projectiveAmbientParameter z e d s J).val, by
        rw [Category.assoc, (projectiveAmbientParameter z e d s J).property, hg]⟩ := by
  apply (allAffineAmbientCharts z).parameterFamily_injective d t
  rw [projectiveAmbientParameter_family, ← AmbientQuotientCharts.parameterFamily_natural,
    projectiveAmbientParameter_family]

end FLT.Mazur.HilbertChart

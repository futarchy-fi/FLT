/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointMarkedCoordinates
public import FLT.Mazur.DivisorComplementCanonical

/-!
# The first-order factor of the original projective X coordinate

The actual included pole-two section is the canonical divisor section times
its original pole-two lift. The remaining factor has coefficient one along the
original marking and generates on a neighborhood containing the entire marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "D" => divisorLineBundle (Scheme.Hom.ker (s)) hI

/-- The original order-two section before inclusion into the projective degree. -/
def completePointPoleTwoSection : Γ(tensorPower (D) 2, ⊤) :=
  moduleH0Equiv _ (completePointPoleLift K n h i 0)

/-- The original homogeneous X contains exactly one explicit canonical divisor factor. -/
theorem completePointProjectiveX_canonicalFactor :
    completePointProjectiveX K n h i =
      SectionGradedMultiplication.cons (D) 2 ⊤ (divisorSection hI ⊤)
        (completePointPoleTwoSection K n h i) := by
  exact (divisorPowerRingStep_sections (exactVeroneseProjToBase K n h).appTop.hom hI 2
    (completePointPoleLift K n h i 0)).trans (divisorTwistedComplex_leftUnitor hI 2 _)

/-- The remaining factor is normalized to one along the original marking. -/
theorem completePointPoleTwoSection_coefficient :
    sectionPoleCoefficient (s) hI (completePointSectionFrame K n h i) 2
      (completePointPoleTwoSection K n h i) = 1 :=
  completePointPoleLift_coefficient K n h i 0

/-- Consequently the remaining factor generates in an actual open containing the marking. -/
theorem completePointPoleTwoSection_contains_marking :
    Set.range (s) ⊆ sectionGeneratorOpen (tensorPower (D) 2)
      (completePointPoleTwoSection K n h i) :=
  sectionPoleGenerator_contains_marking (s) hI (completePointSectionFrame K n h i) 2 _
    (completePointPoleTwoSection_coefficient K n h i)

end FLT.Mazur.PolygonInfinitesimalStages

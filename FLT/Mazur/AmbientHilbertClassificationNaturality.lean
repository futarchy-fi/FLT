/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertFiberSupportCover

/-!
# Natural full-family classification and the common-neighborhood input

Local support is preserved by every base change, and the unique constructed
classifying parameter is natural. A common-affine-neighborhood theorem for
all fibers upgrades the proved equivalence to all full families.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))
variable (g : Y ⟶ X) (hg : g ≫ s = t)

/-- Actual local affine support survives arbitrary test-scheme base change. -/
theorem locallySupportedFamily_baseChange (J : RelativeIdealFamilies z d s)
    (hJ : A.LocallySupportedFamily d s J) :
    A.LocallySupportedFamily d t (relativeIdealFamilyBaseChange z d s t g hg J) := by
  let p := A.locallySupportedParameter d s J hJ
  apply (A.locallySupportedFamily_iff d t _).mpr
  refine ⟨⟨g ≫ p.val, by rw [Category.assoc, p.property, hg]⟩, ?_⟩
  rw [← A.parameterFamily_natural, A.parameterFamily_locallySupportedParameter]

/-- The unique full-family classifying morphism commutes with arbitrary base change. -/
theorem locallySupportedParameter_natural (J : RelativeIdealFamilies z d s)
    (hJ : A.LocallySupportedFamily d s J) :
    A.locallySupportedParameter d t (relativeIdealFamilyBaseChange z d s t g hg J)
        (A.locallySupportedFamily_baseChange d s t g hg J hJ) =
      ⟨g ≫ (A.locallySupportedParameter d s J hJ).val, by
        rw [Category.assoc, (A.locallySupportedParameter d s J hJ).property, hg]⟩ := by
  apply A.parameterFamily_injective d t
  rw [A.parameterFamily_locallySupportedParameter, ← A.parameterFamily_natural,
    A.parameterFamily_locallySupportedParameter]

/-- Common affine neighborhoods for all full fibers yield classification of all full families. -/
def fiberSupportedClassification
    (h : ∀ J : RelativeIdealFamilies z d s, ∀ x : X, ∃ i : A.Index,
      ∀ y : J.val.subscheme, (J.val.subschemeι ≫ pullback.fst s z) y = x →
        (J.val.subschemeι ≫ pullback.snd s z) y ∈ (A.chart i).opensRange) :
    A.GluedParameters d s ≃ RelativeIdealFamilies z d s :=
  Equiv.ofBijective (A.parameterFamily d s) ⟨A.parameterFamily_injective d s, fun J ↦
    (A.existsUnique_parameter_of_fiberSupport d s J (h J)).exists⟩

end FLT.Mazur.HilbertChart.AmbientQuotientCharts

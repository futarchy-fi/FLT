/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertParameterFaithful
public import FLT.Mazur.AmbientHilbertSupportedClassification

/-!
# Compatible Hilbert parameters from local ambient support

Given a base open cover on which each full family lies in an original affine
ambient chart, construct its local parameters and prove their actual overlap
equalities. The input is only support containment of the supplied full family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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

/-- Construct the local glued parameter from the full family's actual affine support. -/
def localSupportedParameter (i : C.I₀) : A.GluedParameters d (C.f i ≫ s) :=
  A.chartParameter d (C.f i ≫ s) (k i)
    (A.supportedParameter d (C.f i ≫ s) (k i)
      (relativeIdealFamilyBaseChange z d s (C.f i ≫ s) (C.f i) rfl J) (hJ i))

/-- Each constructed local parameter recovers the full restricted family. -/
theorem localSupportedParameter_family (i : C.I₀) :
    A.parameterFamily d (C.f i ≫ s) (A.localSupportedParameter d s J C k hJ i) =
      relativeIdealFamilyBaseChange z d s (C.f i ≫ s) (C.f i) rfl J :=
  A.parameterFamily_supportedParameter d (C.f i ≫ s) (k i) _ (hJ i)

/-- The constructed actual local morphisms agree on the full pairwise base intersections. -/
theorem localSupportedParameter_overlap (i j : C.I₀) :
    pullback.fst (C.f i) (C.f j) ≫ (A.localSupportedParameter d s J C k hJ i).val =
      pullback.snd (C.f i) (C.f j) ≫ (A.localSupportedParameter d s J C k hJ j).val := by
  let u := pullback.fst (C.f i) (C.f j)
  let v := pullback.snd (C.f i) (C.f j)
  let t := u ≫ C.f i ≫ s
  have hv : v ≫ C.f j ≫ s = t := by
    dsimp [t, u, v]
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  let p := A.localSupportedParameter d s J C k hJ i
  let q := A.localSupportedParameter d s J C k hJ j
  let p' : A.GluedParameters d t := ⟨u ≫ p.val, by rw [Category.assoc, p.property]⟩
  let q' : A.GluedParameters d t :=
    ⟨v ≫ q.val, by rw [Category.assoc, q.property]; exact hv⟩
  apply congrArg Subtype.val (A.parameterFamily_injective d t (a₁ := p') (a₂ := q') ?_)
  change A.parameterFamily d t ⟨u ≫ p.val, _⟩ = A.parameterFamily d t ⟨v ≫ q.val, _⟩
  rw [← A.parameterFamily_natural d (C.f i ≫ s) t u rfl p,
    ← A.parameterFamily_natural d (C.f j ≫ s) t v hv q]
  change relativeIdealFamilyBaseChange z d _ t u rfl
      (A.parameterFamily d _ (A.localSupportedParameter d s J C k hJ i)) =
    relativeIdealFamilyBaseChange z d _ t v hv
      (A.parameterFamily d _ (A.localSupportedParameter d s J C k hJ j))
  rw [A.localSupportedParameter_family, A.localSupportedParameter_family,
    relativeIdealFamilyBaseChange_comp, relativeIdealFamilyBaseChange_comp]
  congr 1
  exact pullback.condition

end FLT.Mazur.HilbertChart.AmbientQuotientCharts

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstOrderFactor
public import FLT.Mazur.PolygonCompletePointOriginNeighborhood

/-!
# A first-order neighborhood of the entire original marking

Intersect the actual parameter preimage with the generator open of the remaining
pole-two factor. This open still contains the full marking and covers the original
family together with its original Cartier complement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor completeBaseMarking Scheme.Hom.ker

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "D" => divisorLineBundle (Scheme.Hom.ker (s)) hI

/-- The actual parameter neighborhood where the pole-two factor generates. -/
def completePointFirstOrderOpen : (exactVeroneseProj K n h).Opens :=
  completePointOriginOpen K n h i ⊓
    sectionGeneratorOpen (tensorPower (D) 2) (completePointPoleTwoSection K n h i)

/-- The first-order neighborhood retains the entire original marking. -/
theorem completePointMarking_preimage_firstOrder :
    (s) ⁻¹ᵁ completePointFirstOrderOpen K n h i = ⊤ := by
  apply top_unique
  intro x _
  refine ⟨?_, completePointPoleTwoSection_contains_marking K n h i ⟨x, rfl⟩⟩
  exact (show x ∈ (s) ⁻¹ᵁ completePointOriginOpen K n h i from by
    rw [completePointMarking_preimage_origin]; trivial)

/-- The first-order neighborhood and original marking complement cover the whole family. -/
theorem completePointFirstOrderOpen_complement_cover :
    completePointFirstOrderOpen K n h i ⊔ (s).ker.support.compl = ⊤ := by
  let _ := exactVeroneseProjToBase_isProper K n h
  apply top_unique
  intro x _
  by_cases hx : x ∈ (s).ker.support
  · left
    have hx' : x ∈ ((s).ker.support : Set (exactVeroneseProj K n h)) := hx
    rw [support_section_ker (exactVeroneseProjToBase K n h)
      (s) (completeBaseMarking_toBase K n h i)] at hx'
    obtain ⟨z, rfl⟩ := hx'
    exact (show z ∈ (s) ⁻¹ᵁ completePointFirstOrderOpen K n h i from by
      rw [completePointMarking_preimage_firstOrder]; trivial)
  · exact Or.inr hx

/-- Every map into this neighborhood sees the remaining pole-two factor as a generator. -/
theorem completePointFirstOrderOpen_poleTwo_preimage :
    (completePointFirstOrderOpen K n h i).ι ⁻¹ᵁ
      sectionGeneratorOpen (tensorPower (D) 2) (completePointPoleTwoSection K n h i) = ⊤ := by
  apply top_unique
  intro x _
  exact x.property.2

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoordinateBasicOpen
public import FLT.Mazur.GradedProjCoefficientSections
public import FLT.Mazur.CocycleGlobalSectionCoordinate

/-!
# Generator opens of the original homogeneous coefficient sections

An equal positive-degree homogeneous cover identifies each original section's
generator open with its original Proj chart, without changing its normalization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.GradedProjLine

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- The actual coefficient section generates exactly on its homogeneous chart. -/
theorem coefficientSection_generatorOpen (hd : 0 < d)
    (hcover : iSup (chart 𝒜 f) = ⊤) (i : ι) :
    sectionGeneratorOpen (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i) =
      chart 𝒜 f i := by
  have hlocal (j : ι) : (chart 𝒜 f j).ι ⁻¹ᵁ
      sectionGeneratorOpen (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i) =
      (chart 𝒜 f j).ι ⁻¹ᵁ chart 𝒜 f i := by
    refine ((cocycle 𝒜 f hf 1).sectionGeneratorOpen_preimage hcover j _ le_rfl
      (coefficientSection 𝒜 f hf i)).trans ?_
    erw [coefficientSection_evaluate 𝒜 f hf]
    change (chart 𝒜 f j).toScheme.basicOpen ((chart 𝒜 f j).topIso.inv
      (ModuleSheafUnitCocycle.res le_rfl
        (Proj.awayToSection 𝒜 (f j) (coordinate 𝒜 f hf j i)))) = _
    rw [ModuleSheafUnitCocycle.res_self, coordinateSection_basicOpen 𝒜 f hf hd]
  ext x
  have hx : x ∈ iSup (chart 𝒜 f) := by rw [hcover]; trivial
  obtain ⟨j, hx⟩ := Opens.mem_iSup.mp hx
  exact congrArg (fun U : (chart 𝒜 f j).toScheme.Opens ↦
    (⟨x, hx⟩ : (chart 𝒜 f j).toScheme) ∈ U) (hlocal j) |>.to_iff

/-- Every original coefficient section has an affine generator open. -/
theorem coefficientSection_isAffineOpen (hd : 0 < d)
    (hcover : iSup (chart 𝒜 f) = ⊤) (i : ι) :
    IsAffineOpen (sectionGeneratorOpen (line 𝒜 f hf 1)
      (coefficientSection 𝒜 f hf i)) := by
  rw [coefficientSection_generatorOpen 𝒜 f hf hd hcover]
  exact Proj.isAffineOpen_basicOpen 𝒜 (f i) (hf i) hd

end FLT.Mazur.GradedProjLine

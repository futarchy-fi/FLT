/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientGeneratorOpen
public import FLT.Mazur.AmpleAffineBase

/-!
# Ampleness of the original homogeneous coefficient line

On a quasi-compact Proj, a covering equal positive-degree coordinate family
provides affine generator opens for the actual descended coefficient line.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.GradedProjLine

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- The specified coefficient line is ample when its positive-degree charts cover Proj. -/
theorem coefficientLine_ample [CompactSpace (Proj 𝒜)] (hd : 0 < d)
    (hcover : iSup (chart 𝒜 f) = ⊤) : AmpleLineBundle (line 𝒜 f hf 1) := by
  refine ⟨inferInstance, line_rankOne 𝒜 f hf 1 hcover, fun x ↦ ?_⟩
  have hx : x ∈ iSup (chart 𝒜 f) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let e : line 𝒜 f hf 1 ≅ ModuleLineBundleTensorPullback.tensorPower (line 𝒜 f hf 1) 1 :=
    (ModuleSheafTensor.rightUnitor (line 𝒜 f hf 1)).symm
  refine ⟨1, by decide, e.hom.app ⊤ (coefficientSection 𝒜 f hf i), ?_, ?_⟩
  · simpa only [sectionGeneratorOpen_iso,
      coefficientSection_generatorOpen 𝒜 f hf hd hcover] using hi
  · simpa only [sectionGeneratorOpen_iso] using
      coefficientSection_isAffineOpen 𝒜 f hf hd hcover i

/-- The same coefficient line is relatively ample over every affine structural base. -/
theorem coefficientLine_relativelyAmple {S : Scheme} [IsAffine S]
    (p : Proj 𝒜 ⟶ S) [QuasiCompact p] (hd : 0 < d)
    (hcover : iSup (chart 𝒜 f) = ⊤) :
    RelativelyAmpleLineBundle p (line 𝒜 f hf 1) := by
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  exact (coefficientLine_ample 𝒜 f hf hd hcover).relative_of_affine p

end FLT.Mazur.GradedProjLine

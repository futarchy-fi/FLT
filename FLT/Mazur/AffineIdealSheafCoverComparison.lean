/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealSheafComparison
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Detecting ideal equality on an affine open cover

Actual ideal sheaves, including their nilpotent structure, are determined by
their pullbacks to an affine open cover.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.BaseAdicThickening

set_option backward.isDefEq.respectTransparency false

/-- Pullback to all members of an affine open cover detects equality of ideal sheaves. -/
theorem idealSheaf_ext_of_affineCover {X : Scheme.{u}} (C : X.OpenCover)
    [∀ i, IsAffine (C.X i)] {J K : X.IdealSheafData}
    (h : ∀ i, J.comap (C.f i) = K.comap (C.f i)) : J = K := by
  let U : C.I₀ → X.affineOpens := fun i ↦
    ⟨C.f i ''ᵁ ⊤, (isAffineOpen_top (C.X i)).image_of_isOpenImmersion (C.f i)⟩
  apply ext_of_iSup_eq_top U
  · apply top_unique
    intro x _
    obtain ⟨i, y, rfl⟩ := Scheme.Cover.exists_eq C x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, trivial, rfl⟩
  · intro i
    have he := congrArg (fun L : (C.X i).IdealSheafData ↦
      L.ideal ⟨⊤, isAffineOpen_top (C.X i)⟩) (h i)
    rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion] at he
    apply_fun Ideal.comap ((C.f i).appIso ⊤).hom.hom at he
    simpa only [Ideal.comap_comap, ← CommRingCat.hom_comp, Iso.hom_inv_id,
      CommRingCat.hom_id, Ideal.comap_id] using he

end FLT.Mazur.BaseAdicThickening

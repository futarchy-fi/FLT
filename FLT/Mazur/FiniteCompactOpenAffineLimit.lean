/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompactOpenAffineLimit

/-!
# Simultaneous affine descent for finitely many compact opens

One refinement makes an entire finite family of prescribed compact opens
affine whenever all their inverse images in the limit are affine.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- A finite family becomes affine at one common refinement of the specified stage. -/
theorem exists_isAffineOpen_preimages_of_finite {K : Type v} [Finite K]
    (i : I) (U : K → (D.obj i).Opens)
    (hU : ∀ k, IsCompact (U k : Set (D.obj i)))
    (h : ∀ k, IsAffineOpen (c.π.app i ⁻¹ᵁ U k)) :
    ∃ (j : I) (f : j ⟶ i), ∀ k, IsAffineOpen (D.map f ⁻¹ᵁ U k) := by
  classical
  choose j f hj using fun k ↦
    exists_isAffineOpen_preimage_of_isLimit D c hc i (U k) (hU k) (h k)
  cases nonempty_fintype K
  let a (k : K) : Over i := Over.mk (f k)
  obtain ⟨b, hb⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image a)
  refine ⟨b.left, b.hom, fun k ↦ ?_⟩
  let g : b ⟶ a k := (hb (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)).some
  have hg : g.left ≫ f k = b.hom := Over.w g
  have ha := (hj k).preimage (D.map g.left)
  rw [← Scheme.Hom.comp_preimage, ← D.map_comp, hg] at ha
  exact ha

end FLT.Mazur.Approximation

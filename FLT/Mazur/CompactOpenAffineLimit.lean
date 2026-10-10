/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Affineness of compact opens descends along inverse limits

A fixed compact open whose inverse image in the limit is affine becomes
an affine open at a later stage. The open is retained by inverse image,
so the result can be applied to existing chart intersections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Affineness of the inverse image of a compact open occurs at a finite stage. -/
theorem exists_isAffineOpen_preimage_of_isLimit (i : I) (U : (D.obj i).Opens)
    (hU : IsCompact (U : Set (D.obj i))) (h : IsAffineOpen (c.π.app i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i), IsAffineOpen (D.map f ⁻¹ᵁ U) := by
  let _ (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.isOpen hU)
  let _ (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ U).isOpen).mp
      (.of_quasiSeparatedSpace _)
  let _ : IsAffine (opensCone D c i U).pt := h
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc i U)
  exact ⟨j.left, j.hom, hj⟩

end FLT.Mazur.Approximation

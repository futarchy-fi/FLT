/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Schematic closure supported on finitely many sections

A finite union of sections of a separated morphism is closed. If it contains
the generic image, it therefore contains the whole schematic image, including
its special-fiber points. No reducedness of the schematic image is required.
-/

public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.SchematicClosureFiniteSections
universe u v
variable {B X H : Scheme.{u}} (f : X ⟶ B) [IsSeparated f]
  (g : H ⟶ X) [QuasiCompact g] {I : Type v} [Finite I]
  (t : I → (B ⟶ X)) (ht : ∀ a, t a ≫ f = 𝟙 B)

include ht in
omit [Finite I] in
/-- Sections of the separated ambient family are closed immersions. -/
theorem section_closed (a : I) : IsClosedImmersion (t a) := by
  let _ : IsClosedImmersion (t a ≫ f) := by rw [ht]; infer_instance
  exact IsClosedImmersion.of_comp (t a) f

include ht in
/-- The finite section union is closed even when its members meet in the special fiber. -/
theorem section_union_closed : IsClosed (⋃ a, Set.range (t a)) := by
  apply isClosed_iUnion_of_finite
  intro a
  let _ := section_closed f t ht a
  exact (t a).isClosedEmbedding.isClosedMap.isClosed_range

include ht in
/-- Covering the original image by finitely many sections covers its entire schematic closure. -/
theorem image_range_subset
    (hg : Set.range g ⊆ ⋃ a, Set.range (t a)) :
    Set.range g.imageι ⊆ ⋃ a, Set.range (t a) := by
  have hc : IsClosed (g.imageι ⁻¹' (⋃ a, Set.range (t a))) :=
    (section_union_closed f t ht).preimage g.imageι.continuous
  have hd : Set.range g.toImage ⊆ g.imageι ⁻¹' (⋃ a, Set.range (t a)) := by
    rintro _ ⟨x, rfl⟩
    exact hg ⟨x, rfl⟩
  have he := closure_minimal hd hc
  rw [g.toImage.denseRange.closure_range] at he
  rintro _ ⟨x, rfl⟩
  exact he (Set.mem_univ x)

include ht in
/-- Any open containing those actual sections contains the full schematic closure. -/
theorem image_range_subset_open (U : X.Opens)
    (hg : Set.range g ⊆ ⋃ a, Set.range (t a))
    (hU : ∀ a, Set.range (t a) ⊆ U) : Set.range g.imageι ⊆ U := by
  apply (image_range_subset f g t ht hg).trans
  exact Set.iUnion_subset hU

end FLT.Mazur.SchematicClosureFiniteSections

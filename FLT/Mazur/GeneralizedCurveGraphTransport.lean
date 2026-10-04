/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGraph

/-!
# Transport of the actual geometric graph

An equivariant curve isomorphism transports all components, all nonsmooth
points and their incidence. A group isomorphism transports every translation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory TopologicalSpace
namespace FLT.Mazur.GeneralizedCurveGraph
variable {L : Type} [Field L] {G H X Y : Over (Spec (.of L))}
  [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]
  (e : X ≅ Y)

/-- Smoothness of a point is invariant under an isomorphism over the base. -/
theorem smooth_mem_iff (x : X.left) :
    e.hom.left x ∈ Y.hom.smoothLocus ↔ x ∈ X.hom.smoothLocus := by
  have hi : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have he : e.hom.left ⁻¹ᵁ Y.hom.smoothLocus = X.hom.smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    rw! [Over.w]
    rfl
  exact congrArg (fun U : X.left.Opens ↦ x ∈ U) he |>.to_iff

/-- Transport actual irreducible components by their images. -/
def componentEquiv : irreducibleComponents X.left ≃ irreducibleComponents Y.left := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact (irreducibleComponentsEquivOfIsPreirreducibleFiber e.hom.left
    e.hom.left.continuous e.hom.left.isOpenEmbedding.isOpenMap
    (fun _ ↦ isPreirreducible_singleton.preimage e.hom.left.isOpenEmbedding)
    e.hom.left.homeomorph.surjective).symm.toEquiv

/-- Transport every nonsmooth point through the actual scheme isomorphism. -/
def nodeEquiv : {x : X.left // x ∉ X.hom.smoothLocus} ≃
    {y : Y.left // y ∉ Y.hom.smoothLocus} := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact e.hom.left.homeomorph.toEquiv.subtypeEquiv (fun x ↦ not_congr (smooth_mem_iff e x).symm)

omit [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] in
/-- Specialization of an equivariant action commutes with the curve isomorphism. -/
theorem translation_naturality (d : G ≅ H) (a : G ⊗ X ⟶ X) (b : H ⊗ Y ⟶ Y)
    (hab : a ≫ e.hom = (d.hom ⊗ₘ e.hom) ≫ b) (x : 𝟙_ (Over (Spec (.of L))) ⟶ G) :
    translation a x ≫ e.hom = e.hom ≫ translation b (x ≫ d.hom) := by
  simp only [translation, Category.assoc, hab, tensorHom_def', comp_whiskerRight,
    whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

/-- The graph rotation condition transports along equivariant group and curve isomorphisms. -/
theorem rotations_of_iso (d : G ≅ H) (a : G ⊗ X ⟶ X) (b : H ⊗ Y ⟶ Y)
    (hab : a ≫ e.hom = (d.hom ⊗ₘ e.hom) ≫ b) (ha : Rotations a) : Rotations b := by
  obtain ⟨n, hn, v, edges, hinc, hrot⟩ := ha
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hi : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  refine ⟨n, hn, v.trans (componentEquiv e), edges.trans (nodeEquiv e), ?_, ?_⟩
  · intro i j
    change e.hom.left (edges j).val ∈ e.hom.left '' (v i).val ↔ _
    rw [Set.mem_image]
    constructor
    · rintro ⟨x, hx, he⟩
      have he' := e.hom.left.homeomorph.injective he
      exact (hinc i j).mp (he' ▸ hx)
    · intro hij
      exact ⟨_, (hinc i j).mpr hij, rfl⟩
  · intro y
    obtain ⟨r, hv, he⟩ := hrot (y ≫ d.inv)
    have ht : translation a (y ≫ d.inv) ≫ e.hom = e.hom ≫ translation b y := by
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        using translation_naturality e d a b hab (y ≫ d.inv)
    refine ⟨r, ?_, ?_⟩
    · intro i
      change (translation b y).left '' (e.hom.left '' (v i).val) =
        e.hom.left '' (v (PolygonPinching.rotateIndex r i)).val
      rw [← Set.image_comp]
      change (e.hom.left ≫ (translation b y).left) '' (v i).val = _
      rw [← Over.comp_left, ← ht, Over.comp_left]
      change (e.hom.left ∘ (translation a (y ≫ d.inv)).left) '' (v i).val = _
      rw [Set.image_comp, hv]
    · intro j
      change (translation b y).left (e.hom.left (edges j).val) =
        e.hom.left (edges (PolygonPinching.rotateIndex r j)).val
      have hx := congrArg (fun f : X ⟶ Y ↦ f.left (edges j).val) ht
      simpa only [Over.comp_left, Scheme.Hom.comp_apply, he] using hx.symm

end FLT.Mazur.GeneralizedCurveGraph

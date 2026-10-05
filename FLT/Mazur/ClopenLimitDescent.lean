/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Closedness of an open subset descends along an affine inverse limit

Over Noetherian stages, an open subset whose inverse image at the limit is
closed already has closed inverse image at some stage. A compact open
complement descends first; its covering and disjointness identities then
descend to a common stage.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace FLT.Mazur.Approximation

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, NoetherianSpace (D.obj i)]

include hc in
/-- A fixed open becomes closed at a finite stage if it is closed at the limit. -/
theorem exists_isClosed_preimage_of_isLimit {Z : Scheme.{u}}
    (t : D ⟶ (Functor.const I).obj Z) (b : c.pt ⟶ Z)
    (hb : ∀ i, c.π.app i ≫ t.app i = b) (U : Z.Opens)
    (hU : IsClosed ((b ⁻¹ᵁ U : c.pt.Opens) : Set c.pt)) :
    ∃ i, IsClosed ((t.app i ⁻¹ᵁ U : (D.obj i).Opens) : Set (D.obj i)) := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let V : c.pt.Opens := ⟨((b ⁻¹ᵁ U : c.pt.Opens) : Set c.pt)ᶜ, hU.isOpen_compl⟩
  obtain ⟨i, W, _, hW⟩ := AlgebraicGeometry.exists_preimage_eq D c hc V
    ((b ⁻¹ᵁ U).isOpen.isClosed_compl.isCompact)
  let Ui := t.app i ⁻¹ᵁ U
  have hUi : c.π.app i ⁻¹ᵁ Ui = b ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, hb]
  have hsup : c.π.app i ⁻¹ᵁ (Ui ⊔ W) = c.π.app i ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_sup, hUi, hW]
    ext x
    simp [V]
  have hinf : c.π.app i ⁻¹ᵁ (Ui ⊓ W) = c.π.app i ⁻¹ᵁ ⊥ := by
    rw [Scheme.Hom.preimage_inf, hUi, hW]
    ext x
    simp [V]
  obtain ⟨j, fj, hj⟩ := AlgebraicGeometry.exists_map_preimage_eq_map_preimage D c hc
    (isCompact_iff_compactSpace.mpr inferInstance) isCompact_univ hsup
  obtain ⟨k, fk, hk⟩ := AlgebraicGeometry.exists_map_preimage_eq_map_preimage D c hc
    (isCompact_iff_compactSpace.mpr inferInstance) isCompact_empty hinf
  obtain ⟨l, glj, glk, he⟩ := IsCofiltered.cospan fj fk
  have hcover : D.map (glj ≫ fj) ⁻¹ᵁ (Ui ⊔ W) = ⊤ := by
    rw [Functor.map_comp, Scheme.Hom.comp_preimage, hj]
    simp
  have hdisjoint : D.map (glj ≫ fj) ⁻¹ᵁ (Ui ⊓ W) = ⊥ := by
    rw [he, Functor.map_comp, Scheme.Hom.comp_preimage, hk]
    simp
  have hn : D.map (glj ≫ fj) ≫ t.app i = t.app l := by
    simp
  have hcl : IsClosed ((D.map (glj ≫ fj) ⁻¹ᵁ Ui : (D.obj l).Opens) : Set (D.obj l)) := by
    have heq : ((D.map (glj ≫ fj) ⁻¹ᵁ Ui : (D.obj l).Opens) : Set (D.obj l)) =
        ((D.map (glj ≫ fj) ⁻¹ᵁ W : (D.obj l).Opens) : Set (D.obj l))ᶜ := by
      ext x
      have hcov := congrArg (fun O : (D.obj l).Opens ↦ x ∈ O) hcover
      have hdis := congrArg (fun O : (D.obj l).Opens ↦ x ∈ O) hdisjoint
      simp only [Scheme.Hom.preimage_sup, Scheme.Hom.preimage_inf,
        Opens.mem_sup, Opens.mem_inf, Opens.mem_top, Opens.mem_bot] at hcov hdis
      change (_ ∈ Ui) ↔ ¬ (_ ∈ W)
      tauto
    rw [heq]
    exact (D.map (glj ≫ fj) ⁻¹ᵁ W).isOpen.isClosed_compl
  refine ⟨l, ?_⟩
  simpa only [Ui, ← Scheme.Hom.comp_preimage, hn] using hcl

end FLT.Mazur.Approximation

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleImageSection

/-!
# Gluing module sections across two open charts

The additive sheaf condition glues two compatible sections. Via the actual
restriction-to-pullback comparisons, sections on two open charts glue when
they agree on a common chart covering the full intersection of their images.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}}
/-- Two sections with equal restrictions on an intersection glue over a binary cover. -/
lemma binary_section_glue (M : X.Modules) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (s : Γ(M, U)) (t : Γ(M, V))
    (hst : M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s =
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op t) :
    ∃ r : Γ(M, ⊤), M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r = s ∧
      M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op r = t := by
  let C : Bool → X.Opens := Bool.rec U V
  let v : ∀ i, Γ(M, C i) := Bool.rec s t
  have hC : (⊤ : X.Opens) ≤ ⨆ i, C i := by
    simpa only [iSup_bool_eq, C, sup_comm] using hcover.ge
  have hv : TopCat.Presheaf.IsCompatible M.presheaf C v := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact hst
    · have hh := congrArg (M.presheaf.map (eqToHom (inf_comm V U)).op) hst.symm
      simpa only [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp,
        ← op_comp, eqToHom_comp_homOfLE, C, v, TopologicalSpace.Opens.infLELeft,
        TopologicalSpace.Opens.infLERight] using hh
    · rfl
  obtain ⟨r, hr, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) C ⊤
    (fun _ ↦ homOfLE le_top) hC v hv
  exact ⟨r, hr false, hr true⟩
/-- Equal common pullbacks give an actual global section with both prescribed pullbacks. -/
lemma pullOverlap_exists_glue {Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (j : Y ⟶ Z) (g : X ⟶ W) (k : W ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion g] [IsOpenImmersion k]
    (h : f ≫ j = g ≫ k) (M : Z.Modules)
    (s : Γ((pullback j).obj M, ⊤)) (t : Γ((pullback k).obj M, ⊤))
    (hab : pullOverlap f j M s = pullOverlapAlong g k (f ≫ j) h.symm M t)
    (hi : j ''ᵁ ⊤ ⊓ k ''ᵁ ⊤ ≤ (f ≫ j) ''ᵁ ⊤)
    (hc : j ''ᵁ ⊤ ⊔ k ''ᵁ ⊤ = ⊤) :
    ∃ r : Γ(M, ⊤), pullGlobal j M r = s ∧ pullGlobal k M r = t := by
  obtain ⟨r, hs, ht⟩ := binary_section_glue M _ _ hc (imageSection j M s)
    (imageSection k M t) (pullOverlap_compatible f j g k h M s t hab hi)
  refine ⟨r, ?_, ?_⟩
  · have hh := congrArg (((restrictFunctorIsoPullback j).hom.app M).app ⊤) hs
    simpa only [pullGlobal_restrict, pullGlobal_imageSection] using hh
  · have hh := congrArg (((restrictFunctorIsoPullback k).hom.app M).app ⊤) ht
    simpa only [pullGlobal_restrict, pullGlobal_imageSection] using hh
end FLT.Mazur.FCurve

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleImageSection
public import Mathlib.Algebra.Category.Grp.Zero
/-!
# Arbitrary module sections on disjoint covers

Disjoint chart sections glue uniquely by the sheaf condition. This applies to
arbitrary module sheaves and does not restrict to structure-sheaf constants.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}}
/-- Sections on pairwise disjoint opens glue over their union. -/
lemma disjoint_section_glue (M : X.Modules) {ι : Type v} (U : ι → X.Opens)
    (hd : Pairwise (fun i j ↦ Disjoint (U i) (U j))) (hc : iSup U = ⊤)
    (s : ∀ i, Γ(M, U i)) :
    ∃ t : Γ(M, ⊤), ∀ i, M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op t = s i := by
  have hs : TopCat.Presheaf.IsCompatible M.presheaf U s := by
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · have hij : U i ⊓ U j = ⊥ := (hd h).eq_bot
      have : Subsingleton (M.presheaf.obj (op (U i ⊓ U j))) := by
        rw [hij]
        exact AddCommGrpCat.subsingleton_of_isZero
          ((CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
            ((TopCat.Sheaf.isTerminalOfEmpty
              (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)).hom_ext _ _))
      exact Subsingleton.elim _ _
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) U ⊤
    (fun _ ↦ homOfLE le_top) hc.ge s hs
  exact ⟨t, ht⟩
/-- Pullback to a disjoint open cover is a bijection on families of global sections. -/
lemma pullGlobal_disjointCover_bijective (C : X.OpenCover)
    (hd : Pairwise (fun i j ↦ Disjoint (C.f i ''ᵁ ⊤) (C.f j ''ᵁ ⊤)))
    (M : X.Modules) : Function.Bijective (fun s : Γ(M, ⊤) ↦ fun i ↦ pullGlobal (C.f i) M s) := by
  constructor
  · intro s t h
    exact pullGlobal_openCover_ext C M s t (fun i ↦ congrFun h i)
  · intro s
    obtain ⟨t, ht⟩ := disjoint_section_glue M (fun i ↦ C.f i ''ᵁ ⊤) hd
      (by simpa only [Scheme.Hom.image_top_eq_opensRange] using C.iSup_opensRange)
      (fun i ↦ imageSection (C.f i) M (s i))
    refine ⟨t, funext fun i ↦ ?_⟩
    have he := congrArg (((restrictFunctorIsoPullback (C.f i)).hom.app M).app ⊤) (ht i)
    simpa only [pullGlobal_restrict, pullGlobal_imageSection] using he
end FLT.Mazur.FCurve

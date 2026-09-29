/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechInjectiveAcyclic

/-!
# Relative Cech vanishing for injective sheaves

The free Cech complex is exact in positive degrees for any family of opens.
At a point in the union, insertion contracts it; outside the union its terms
vanish. Applying Hom into an injective therefore gives positive Cech exactness
without requiring the family to cover the whole space.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology
open scoped Simplicial

universe u

namespace FLT.Mazur.AffineCohomologyVanishingRelInjective

open CechFreeOpen CechFreeResolution CechSheafHZero CechInjectiveAcyclic

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- Outside the union, every term of the free complex has zero stalk. -/
lemma freeComplex_stalk_isZero (x : X) (hx : x ∉ iSup U) (n : ℕ) :
    IsZero ((sheafStalk x).obj ((freeComplex U).X n)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply stalkGenerator_hom_ext U n x
  intro a p z
  exact False.elim (hx (Opens.mem_iSup.mpr
    ⟨a 0, (iInf_le (fun j ↦ U (a j)) 0) p.down.down⟩))

/-- On the union, the existing stalk insertion contracts positive degrees. -/
lemma freeComplex_stalk_exactAt_of_mem (x : X) (i : ι) (hi : x ∈ U i) (n : ℕ) :
    (((sheafStalk x).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (freeComplex U)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro z hz
  let ed := freeStalkExtraDegeneracy U x i hi
  refine ⟨ed.s (n + 1) z, ?_⟩
  have h := ConcreteCategory.congr_hom
    (extraDegeneracy_contraction_succ (freeStalkAugmented U x) ed n) z
  rw [freeStalkComplex_d, freeStalkComplex_d, AddCommGrpCat.hom_add_apply] at h
  change (sheafStalk x).map ((freeComplex U).d (n + 1) n) z = 0 at hz
  have hzero : ((sheafStalk x).map ((freeComplex U).d (n + 1) n) ≫ ed.s n) z = 0 := by
    change ed.s n ((sheafStalk x).map ((freeComplex U).d (n + 1) n) z) = 0
    rw [hz, map_zero]
  erw [hzero, add_zero] at h
  exact h

/-- Positive free-complex exactness on stalks does not require a cover of the space. -/
lemma freeComplex_stalk_exactAt_relative (x : X) (n : ℕ) :
    (((sheafStalk x).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (freeComplex U)).ExactAt (n + 1) := by
  classical
  by_cases hx : x ∈ iSup U
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact freeComplex_stalk_exactAt_of_mem U x i hi n
  · exact ShortComplex.exact_of_isZero_X₂ _ (freeComplex_stalk_isZero U x hx (n + 1))

/-- Stalkwise exactness descends to the unaugmented free complex. -/
lemma freeComplex_exactAt_relative (n : ℕ) : (freeComplex U).ExactAt (n + 1) := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  exact freeComplex_stalk_exactAt_relative U x n

/-- Hom into an injective is exact on the relative free complex in positive degrees. -/
lemma hom_exact_of_injective_relative
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] (n : ℕ)
    (f : (freeComplex U).X (n + 1) ⟶ I)
    (hf : (freeComplex U).d (n + 2) (n + 1) ≫ f = 0) :
    ∃ g : (freeComplex U).X n ⟶ I, (freeComplex U).d (n + 1) n ≫ g = f := by
  have h := (HomologicalComplex.exactAt_iff' (freeComplex U)
    (n + 2) (n + 1) n (by simp) (by simp)).mp (freeComplex_exactAt_relative U n)
  have he := h.op.map (preadditiveYonedaObj I)
  rw [ShortComplex.moduleCat_exact_iff] at he
  exact he f hf

/-- Injective coefficients have exact positive Cech degrees for any family of opens. -/
lemma cech_exactAt_of_injective_relative
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] (n : ℕ) :
    (C U I).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro z hz
  change (C U I).d (n + 1) (n + 2) z = 0 at hz
  let f := (homTermEquiv U I (n + 1)).symm z
  have hf : (freeComplex U).d (n + 2) (n + 1) ≫ f = 0 := by
    apply (homTermEquiv U I (n + 2)).injective
    rw [homTermEquiv_d, map_zero]
    simpa only [f, AddEquiv.apply_symm_apply] using hz
  obtain ⟨g, hg⟩ := hom_exact_of_injective_relative U I n f hf
  refine ⟨homTermEquiv U I n g, ?_⟩
  change (C U I).d n (n + 1) _ = z
  rw [← homTermEquiv_d, hg]
  exact (homTermEquiv U I (n + 1)).apply_symm_apply z

/-- Positive relative Cech cohomology of an injective is zero. -/
lemma cech_isZero_of_injective_relative
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] (n : ℕ) :
    IsZero (CH U I (n + 1)) :=
  (cech_exactAt_of_injective_relative U I n).isZero_homology

end FLT.Mazur.AffineCohomologyVanishingRelInjective

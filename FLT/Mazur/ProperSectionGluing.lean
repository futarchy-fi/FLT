/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.GenericSectionUniqueness
public import FLT.Mazur.ProperStalkExtension

/-!
# Gluing proper extensions over an integral base

On a separated integral scheme whose stalks are valuation rings, every
function-field point of a proper scheme extends uniquely to a section.
The proof spreads the valuative lifts at all stalks. Their common rational map
has domain the whole base; Mathlib's maximal partial map glues the lifts using
separatedness. No local or global extension is included among the hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur

/-- The generic stalk of an integral scheme maps dominantly to that scheme. -/
theorem genericStalk_isDominant (S : Scheme.{u}) [IsIntegral S] :
    IsDominant (S.fromSpecStalk (genericPoint S)) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← genericPoint_closure (α := S)]
  apply closure_mono
  intro s hs
  rcases Set.mem_singleton_iff.mp hs with rfl
  exact ⟨IsLocalRing.closedPoint (S.presheaf.stalk (genericPoint S)),
    Scheme.fromSpecStalk_closedPoint⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Glue valuative extensions into a unique global section. -/
theorem Sections.existsUnique_of_valuation_stalks (S : Scheme.{u})
    [IsIntegral S] [S.IsSeparated]
    [∀ s : S, ValuationRing (S.presheaf.stalk s)]
    (X : Over S) [IsProper X.hom]
    (x : Points X (S.fromSpecStalk (genericPoint S))) :
    ∃! y : Sections X, Sections.restrict (S.fromSpecStalk (genericPoint S)) y = x := by
  let : IsDominant (S.fromSpecStalk (genericPoint S)) := genericStalk_isDominant S
  have : X.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance
  let r := Scheme.RationalMap.ofFunctionField (𝟙 S) X.hom x.left
    (by simp)
  have hr : r.fromFunctionField = x.left :=
    Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have hdom : r.domain = ⊤ := by
    apply top_le_iff.mp
    intro s _
    obtain ⟨f, hs, _, hf⟩ := exists_partialMap_at_valuation_stalk X x s
    exact Scheme.RationalMap.mem_domain.mpr ⟨f, hs,
      Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ (hf.trans hr.symm)⟩
  let f := r.toPartialMap
  have hf : f.fromFunctionField = x.left := by
    rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.toRationalMap_toPartialMap]
    exact hr
  have hd : f.domain = ⊤ := hdom
  let : IsIso f.domain.ι := by
    rw [hd]
    change IsIso S.topIso.hom
    infer_instance
  let g : S ⟶ X.left := inv f.domain.ι ≫ f.hom
  have hg : S.fromSpecStalk (genericPoint S) ≫ g = x.left := by
    rw [← hf]
    unfold Scheme.PartialMap.fromFunctionField Scheme.PartialMap.fromSpecStalkOfMem
    dsimp only [g]
    rw [← Category.assoc]
    congr 1
    apply (cancel_mono f.domain.ι).mp
    simp
  have hover : g ≫ X.hom = 𝟙 S := by
    apply ext_of_isDominant (S.fromSpecStalk (genericPoint S))
    rw [← Category.assoc, hg, Over.w x, Category.comp_id]
    rfl
  refine ⟨Over.homMk g hover, Over.OverMorphism.ext hg, ?_⟩
  intro y hy
  apply Sections.restrict_injective_of_dominant X (S.fromSpecStalk (genericPoint S))
  exact hy.trans (Over.OverMorphism.ext hg).symm

end FLT.Mazur

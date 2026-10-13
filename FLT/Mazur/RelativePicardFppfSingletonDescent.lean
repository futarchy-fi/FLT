/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfSheafCriterion
public import FLT.Mazur.RelativePicardFppfSheaf
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

/-!
# Original Picard sections descend along an actual fppf kernel pair

Equality on the two scheme pullback projections constructs a unique section
on the target. This keeps descent of a translating section separate from
scheme effectivity of its full parameter relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]

/-- An actual singleton fppf cover satisfies the original Picard sheaf condition. -/
theorem relativePicardFppf_singleton_isSheafFor :
    Presieve.IsSheafFor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (Presieve.singleton b) := by
  have hs := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  apply hs.isSheafFor
  rw [← Presieve.ofArrows_pUnit.{0}, ← Sieve.ofArrows,
    GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  rw [Presieve.ofArrows_pUnit]
  exact Scheme.Hom.singleton_mem_fppfPrecoverage b.left

/-- Compatibility on the actual scheme kernel pair constructs a unique original section. -/
theorem relativePicardFppf_singleton_existsUnique
    (c : (relativeFppfSheaf f).obj.obj (op W))
    (hc : (relativeFppfSheaf f).obj.map (pullback.fst b b).op c =
      (relativeFppfSheaf f).obj.map (pullback.snd b b).op c) :
    ∃! t : (relativeFppfSheaf f).obj.obj (op V),
      (relativeFppfSheaf f).obj.map b.op t = c := by
  have hs := relativePicardFppf_singleton_isSheafFor f b
  rw [Presieve.isSheafFor_singleton] at hs
  apply hs c
  intro T p q hpq
  let k := pullback.lift p q hpq
  have hk₁ : k ≫ pullback.fst b b = p := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd b b = q := pullback.lift_snd _ _ _
  change (relativeFppfSheaf f).obj.map p.op c = (relativeFppfSheaf f).obj.map q.op c
  rw [← hk₁, ← hk₂]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hc]

/-- Pullback by the actual fppf cover detects equality of original Picard sections. -/
theorem relativePicardFppf_singleton_injective :
    Function.Injective ((relativeFppfSheaf f).obj.map b.op) := by
  have hs := (relativePicardFppf_singleton_isSheafFor f b).isSeparatedFor
  rwa [Presieve.isSeparatedFor_singleton] at hs

end FLT.Mazur.SchemePicard

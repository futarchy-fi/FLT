/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryFaithfulOpen

/-!
# Every faithful original boundary test lifts to the constructed open

Universal distinctness of the original pulled-back sections excludes the entire
kernel schemes. The lift preserves all original auxiliary and cyclic labels.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom] (n : ℕ) [NeZero n]
  {T : Scheme} (g : T ⟶ S) (f : Over.mk g ⟶ parameter E n)
  (hf : UniversallyDistinctSections.UniversallyDistinct
    (fun i : ZMod n ↦ cyclicSectionMarking E n g f (.ofAdd i)))

include hf in
omit [IsSeparated E.hom] in
/-- The original distinct cyclic sections are universally faithful in the equation scheme. -/
theorem cyclicProjection_universallyFaithful :
    AuxiliaryLevel.UniversallyFaithful E (Multiplicative (ZMod n))
      (f ≫ cyclicProjection E n) := by
  intro V k hV i j hij
  let U : Over T := Over.mk k.left
  let a : U ⟶ 𝟙_ (Over T) := Over.homMk k.left (by simp [U])
  apply Multiplicative.toAdd.injective
  apply hf U a hV
  apply OverPullbackSection.hom_ext
  change (k ≫ f ≫ cyclicProjection E n) ≫ AuxiliaryLevel.value E _ i =
    (k ≫ f ≫ cyclicProjection E n) ≫ AuxiliaryLevel.value E _ j at hij
  simp only [Category.assoc, cyclicProjection_value] at hij
  have he := congrArg Over.Hom.left hij
  simpa only [Over.comp_left, Category.assoc, cyclicSectionMarking_apply,
    section_fst, ofAdd_toAdd, a, Over.homMk_left, U] using he

/-- The actual faithful lift of an original boundary parameter test. -/
def cyclicFaithfulLift : Over.mk g ⟶ cyclicFaithfulParameter E n := by
  change Over.mk g ⟶ Over.mk ((cyclicFaithfulOpen E n).ι ≫ (parameter E n).hom)
  exact Over.homMk (IsOpenImmersion.lift (cyclicFaithfulOpen E n).ι f.left (by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨f.left x, ?_⟩, rfl⟩
    exact AuxiliaryLevel.universallyFaithful_range E (Multiplicative (ZMod n))
      (f ≫ cyclicProjection E n) (cyclicProjection_universallyFaithful E n g f hf)
      ⟨x, rfl⟩)) (by
        change _ ≫ (cyclicFaithfulOpen E n).ι ≫ (parameter E n).hom = g
        rw [IsOpenImmersion.lift_fac_assoc, f.w]
        rfl)

/-- The lift retains the entire original parameter, not merely its point set. -/
@[reassoc] theorem cyclicFaithfulLift_inclusion :
    cyclicFaithfulLift E n g f hf ≫ cyclicFaithfulInclusion E n = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- Universal distinctness is represented exactly by the constructed faithful open. -/
theorem cyclicFaithful_iff_existsUnique :
    UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ cyclicSectionMarking E n g f (.ofAdd i)) ↔
      ∃! v : Over.mk g ⟶ cyclicFaithfulParameter E n,
        v ≫ cyclicFaithfulInclusion E n = f := by
  constructor
  · intro hs
    refine ⟨cyclicFaithfulLift E n g f hs, cyclicFaithfulLift_inclusion E n g f hs, ?_⟩
    intro v hv
    apply Over.OverMorphism.ext
    apply (cancel_mono (cyclicFaithfulOpen E n).ι).mp
    exact congrArg Over.Hom.left (hv.trans (cyclicFaithfulLift_inclusion E n g f hs).symm)
  · rintro ⟨v, rfl, _⟩
    exact cyclicFaithfulSection_distinct E n g v

end FLT.Mazur.CyclicBoundaryParameter

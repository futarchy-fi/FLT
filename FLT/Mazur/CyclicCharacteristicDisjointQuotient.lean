/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointAction

/-!
# The actual quotient of the single disjoint-union source

The component quotient maps assemble into one invariant surjective morphism.
The component universal properties prove the full categorical quotient
property for the actual assembled relabeling action and arbitrary targets.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The single scheme assembling both constructed characteristic quotients. -/
def normalizedDisjointQuotient : Scheme := ∐ normalizedQuotient n

/-- The original characteristic quotient includes into the assembled quotient. -/
def normalizedDisjointQuotientInclusion (b : Bool) :
    normalizedQuotient n b ⟶ normalizedDisjointQuotient n := Sigma.ι (normalizedQuotient n) b

/-- The original characteristic quotient is an open component of the union. -/
instance normalizedDisjointQuotientInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (normalizedDisjointQuotientInclusion n b) := by
  unfold normalizedDisjointQuotientInclusion
  infer_instance

/-- The actual quotient morphisms on both original source components assemble. -/
def normalizedDisjointQuotientMap : normalizedDisjointSource n ⟶ normalizedDisjointQuotient n :=
  Sigma.desc (fun b => normalizedQuotientMap n b ≫ normalizedDisjointQuotientInclusion n b)

/-- The assembled quotient retains the original quotient morphism on each component. -/
@[reassoc] theorem normalizedDisjointInclusion_quotientMap (b : Bool) :
    normalizedDisjointInclusion n b ≫ normalizedDisjointQuotientMap n =
      normalizedQuotientMap n b ≫ normalizedDisjointQuotientInclusion n b :=
  Sigma.ι_comp_desc _ b

/-- The single quotient map is invariant under the assembled actual group action. -/
@[reassoc] theorem normalizedDisjointQuotientMap_invariant (g : RelabelGroup n) :
    (normalizedDisjointAction n g).hom ≫ normalizedDisjointQuotientMap n =
      normalizedDisjointQuotientMap n := by
  apply Sigma.hom_ext
  intro b
  change normalizedDisjointInclusion n b ≫ _ = normalizedDisjointInclusion n b ≫ _
  rw [normalizedDisjointAction_inclusion_assoc, normalizedDisjointInclusion_quotientMap,
    normalizedQuotientMap_invariant_assoc]

/-- Every point of the single quotient has a representative in the original union. -/
instance normalizedDisjointQuotientMap_surjective :
    Surjective (normalizedDisjointQuotientMap n) := by
  constructor
  intro z
  obtain ⟨b, y, rfl⟩ := (sigmaOpenCover (normalizedQuotient n)).exists_eq z
  obtain ⟨x, rfl⟩ := (normalizedQuotientMap n b).surjective y
  refine ⟨normalizedDisjointInclusion n b x, ?_⟩
  exact congrArg (fun f ↦ f x) (normalizedDisjointInclusion_quotientMap n b)

/-- Any invariant morphism from the actual assembled source descends uniquely. -/
theorem normalizedDisjointQuotientMap_existsUnique_desc {Y : Scheme}
    (f : normalizedDisjointSource n ⟶ Y)
    (hf : ∀ g : RelabelGroup n, (normalizedDisjointAction n g).hom ≫ f = f) :
    ∃! k : normalizedDisjointQuotient n ⟶ Y, normalizedDisjointQuotientMap n ≫ k = f := by
  have hi (b : Bool) (g : RelabelGroup n) :
      (normalizedRelabelAction n b g).hom ≫ normalizedDisjointInclusion n b ≫ f =
        normalizedDisjointInclusion n b ≫ f := by
    rw [← normalizedDisjointAction_inclusion_assoc, hf]
  choose k hk hu using fun b => normalizedQuotientMap_existsUnique_desc n b
    (normalizedDisjointInclusion n b ≫ f) (hi b)
  refine ⟨Sigma.desc k, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro b
    change normalizedDisjointInclusion n b ≫ _ = normalizedDisjointInclusion n b ≫ _
    rw [normalizedDisjointInclusion_quotientMap_assoc]
    change normalizedQuotientMap n b ≫ (Sigma.ι _ b ≫ Sigma.desc k) = _
    rw [Sigma.ι_comp_desc, hk]
  · intro l hl
    apply Sigma.hom_ext
    intro b
    rw [Sigma.ι_comp_desc]
    apply hu b
    change normalizedQuotientMap n b ≫ normalizedDisjointQuotientInclusion n b ≫ l = _
    rw [← normalizedDisjointInclusion_quotientMap_assoc, hl]

end FLT.Mazur.CyclicCharacteristicAtlas

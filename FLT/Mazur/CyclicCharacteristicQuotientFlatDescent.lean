/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicQuotient
public import FLT.Mazur.StableAffineQuotientFlatDescent

/-!
# Flat base change of the actual characteristic quotients

The actual relabeling action lifts to each base-changed normalized source.
After an arbitrary flat base change, the original quotient projection still
has the categorical quotient universal property for every scheme target.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) {S : Scheme}
  (f : S ⟶ normalizedQuotient n b)

/-- The original common relabeling action on the actual base-changed normalized source. -/
def normalizedQuotientBaseChangeAction :
    RelabelGroup n →* Aut (pullback (normalizedQuotientMap n b) f) :=
  FiniteGroupPullback.action (normalizedRelabelAction n b) (normalizedQuotientMap n b)
    (normalizedQuotientMap_invariant n b) f

/-- The first base-change projection retains the exact original relabeling action. -/
@[reassoc] theorem normalizedQuotientBaseChangeAction_fst (g : RelabelGroup n) :
    (normalizedQuotientBaseChangeAction n b f g).hom ≫
        pullback.fst (normalizedQuotientMap n b) f =
      pullback.fst (normalizedQuotientMap n b) f ≫ (normalizedRelabelAction n b g).hom :=
  FiniteGroupPullback.action_fst _ _ _ _ g

/-- The actual projection to the new base is invariant. -/
@[reassoc] theorem normalizedQuotientBaseChangeAction_snd (g : RelabelGroup n) :
    (normalizedQuotientBaseChangeAction n b f g).hom ≫
        pullback.snd (normalizedQuotientMap n b) f =
      pullback.snd (normalizedQuotientMap n b) f :=
  FiniteGroupPullback.action_snd _ _ _ _ g

variable [Flat f] {Y : Scheme} (k : pullback (normalizedQuotientMap n b) f ⟶ Y)

/-- Invariant maps from the actual flat base change descend uniquely to the new base. -/
theorem normalizedQuotient_existsUnique_flatDesc
    (hk : ∀ g : RelabelGroup n, (normalizedQuotientBaseChangeAction n b f g).hom ≫ k = k) :
    ∃! d : S ⟶ Y, pullback.snd (normalizedQuotientMap n b) f ≫ d = k :=
  StableAffineQuotient.existsUnique_flatDesc (normalizedRelabelAction n b)
    (FiniteGroupNeighborhoodCover.stableCharts_cover _
      (normalizedLocus_hasFiniteNeighborhoods n b)) f k hk

/-- The categorical quotient condition remains exact on arbitrary flat new bases. -/
theorem normalizedQuotient_invariant_iff_existsUnique_flatDesc :
    (∀ g : RelabelGroup n, (normalizedQuotientBaseChangeAction n b f g).hom ≫ k = k) ↔
      ∃! d : S ⟶ Y, pullback.snd (normalizedQuotientMap n b) f ≫ d = k := by
  constructor
  · exact normalizedQuotient_existsUnique_flatDesc n b f k
  · rintro ⟨d, hd, _⟩ g
    rw [← hd, normalizedQuotientBaseChangeAction_snd_assoc]

end FLT.Mazur.CyclicCharacteristicAtlas

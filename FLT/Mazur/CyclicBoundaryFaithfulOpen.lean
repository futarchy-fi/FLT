/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryGroupSections
public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation
public import FLT.Mazur.UniversallyDistinctSections

/-!
# The cyclically faithful open in the original boundary parameter

Only the cyclic factor is required to be faithful. The independent auxiliary
markings remain unrestricted. The actual open inclusion retains every label.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] (n : ℕ) [NeZero n]

/-- The cyclic factor of the universal boundary marking. -/
def universalCyclicMarking : Multiplicative (ZMod n) →* (parameter E n ⟶ E) where
  toFun j := AuxiliaryLevel.value E (Label n) (1, 1, j)
  map_one' := (AuxiliaryLevel.universalMarking E (Label n)).map_one
  map_mul' i j := by
    simpa only [Prod.mk_mul_mk, _root_.one_mul] using
      AuxiliaryLevel.value_mul E (Label n) (1, 1, i) (1, 1, j)

/-- Forget the auxiliary labels without changing the original cyclic marking. -/
def cyclicProjection : parameter E n ⟶ AuxiliaryLevel.homScheme E (Multiplicative (ZMod n)) :=
  AuxiliaryLevel.liftMarking E _ (universalCyclicMarking E n)

/-- Projection retains each actual cyclic label. -/
@[reassoc] theorem cyclicProjection_value (j : Multiplicative (ZMod n)) :
    cyclicProjection E n ≫ AuxiliaryLevel.value E _ j =
      AuxiliaryLevel.value E (Label n) (1, 1, j) :=
  AuxiliaryLevel.liftMarking_value _ _ _ _

variable [IsSeparated E.hom]

/-- The original parameter open on which the cyclic factor is universally faithful. -/
def cyclicFaithfulOpen : (parameter E n).left.Opens :=
  (cyclicProjection E n).left ⁻¹ᵁ AuxiliaryLevel.faithfulOpen E (Multiplicative (ZMod n))

/-- The faithful boundary parameter retains its original coefficient morphism. -/
def cyclicFaithfulParameter : Over S :=
  Over.mk ((cyclicFaithfulOpen E n).ι ≫ (parameter E n).hom)

/-- The actual open inclusion in the full boundary parameter. -/
def cyclicFaithfulInclusion : cyclicFaithfulParameter E n ⟶ parameter E n :=
  Over.homMk (cyclicFaithfulOpen E n).ι rfl

/-- Restriction to the cyclic factor lands in its actual faithful scheme. -/
def cyclicFaithfulProjection :
    cyclicFaithfulParameter E n ⟶ AuxiliaryLevel.faithfulScheme E (Multiplicative (ZMod n)) :=
  Over.homMk
    (IsOpenImmersion.lift (AuxiliaryLevel.faithfulOpen E (Multiplicative (ZMod n))).ι
      ((cyclicFaithfulOpen E n).ι ≫ (cyclicProjection E n).left) (by
        rintro _ ⟨x, rfl⟩
        exact ⟨⟨_, x.property⟩, rfl⟩)) (by
          change _ ≫ (AuxiliaryLevel.faithfulOpen E (Multiplicative (ZMod n))).ι ≫ _ = _
          rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, (cyclicProjection E n).w]
          rfl)

/-- The two actual projections agree on the entire original cyclic equation scheme. -/
@[reassoc] theorem cyclicFaithfulProjection_inclusion :
    cyclicFaithfulProjection E n ≫ AuxiliaryLevel.faithfulInclusion E _ =
      cyclicFaithfulInclusion E n ≫ cyclicProjection E n := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- All cyclic labels are universally distinct on every test of the faithful open. -/
theorem cyclicFaithfulSection_distinct {T : Scheme} (g : T ⟶ S)
    (f : Over.mk g ⟶ cyclicFaithfulParameter E n) :
    UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦
      cyclicSectionMarking E n g (f ≫ cyclicFaithfulInclusion E n) (.ofAdd i)) := by
  intro V k hV i j hij
  let _ : Nonempty (Over.mk (k.left ≫ g)).left := hV
  let a : Over.mk (k.left ≫ g) ⟶ Over.mk g := Over.homMk k.left rfl
  have hinj := AuxiliaryLevel.faithful_marking_injective E (Multiplicative (ZMod n))
    (a ≫ f ≫ cyclicFaithfulProjection E n)
  apply Multiplicative.ofAdd.injective
  apply hinj
  change (a ≫ f ≫ cyclicFaithfulProjection E n) ≫
      AuxiliaryLevel.faithfulInclusion E _ ≫ AuxiliaryLevel.value E _ (.ofAdd i) =
    (a ≫ f ≫ cyclicFaithfulProjection E n) ≫
      AuxiliaryLevel.faithfulInclusion E _ ≫ AuxiliaryLevel.value E _ (.ofAdd j)
  simp only [Category.assoc, cyclicFaithfulProjection_inclusion_assoc,
    cyclicProjection_value]
  apply Over.OverMorphism.ext
  have he := congrArg (fun z ↦ z.left ≫ pullback.fst E.hom g) hij
  simpa only [Over.comp_left, Category.assoc, cyclicSectionMarking_apply,
    section_fst, a, Over.homMk_left] using he

end FLT.Mazur.CyclicBoundaryParameter

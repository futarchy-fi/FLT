/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicGlobalRetraction

/-!
# The represented relation of equal full normalizations

The relation retains both original coefficient maps and every cyclic label.
It is the actual kernel pair of the full slice map. Identification with all
marked isomorphisms is a separate assertion, not part of this definition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n]

/-- Pairs of original full parameters with the same complete normalized parameter. -/
def cyclicNormalizationRelation : Scheme :=
  pullback (cyclicNormalizationSliceMap n) (cyclicNormalizationSliceMap n)

/-- The first original parameter in the represented normalization relation. -/
def cyclicNormalizationRelationFirst :
    cyclicNormalizationRelation n ⟶ (cyclicAuxiliaryScheme n).left :=
  pullback.fst _ _

/-- The second original parameter in the represented normalization relation. -/
def cyclicNormalizationRelationSecond :
    cyclicNormalizationRelation n ⟶ (cyclicAuxiliaryScheme n).left :=
  pullback.snd _ _

/-- The represented relation equates the actual full normalized slice points. -/
@[reassoc] theorem cyclicNormalizationRelation_condition :
    cyclicNormalizationRelationFirst n ≫ cyclicNormalizationSliceMap n =
      cyclicNormalizationRelationSecond n ≫ cyclicNormalizationSliceMap n :=
  pullback.condition

/-- Equal independent normalizations give a point of the actual relation scheme. -/
def cyclicNormalizationRelationPoint {T : Scheme}
    (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
    (h : cyclicSchemeNormalizedSlicePoint n f = cyclicSchemeNormalizedSlicePoint n g) :
    T ⟶ cyclicNormalizationRelation n :=
  pullback.lift f g (by
    simpa only [cyclicSchemeNormalizedSlicePoint_eq_natural,
      cyclicNaturalNormalizedSlicePoint] using h)

/-- The relation point retains its first original coefficient map and full labeling. -/
@[reassoc] theorem cyclicNormalizationRelationPoint_first {T : Scheme}
    (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
    (h : cyclicSchemeNormalizedSlicePoint n f = cyclicSchemeNormalizedSlicePoint n g) :
    cyclicNormalizationRelationPoint n f g h ≫ cyclicNormalizationRelationFirst n = f :=
  pullback.lift_fst _ _ _

/-- The relation point retains its second original coefficient map and full labeling. -/
@[reassoc] theorem cyclicNormalizationRelationPoint_second {T : Scheme}
    (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
    (h : cyclicSchemeNormalizedSlicePoint n f = cyclicSchemeNormalizedSlicePoint n g) :
    cyclicNormalizationRelationPoint n f g h ≫ cyclicNormalizationRelationSecond n = g :=
  pullback.lift_snd _ _ _

/-- Both original parameters uniquely determine a morphism into the relation. -/
theorem cyclicNormalizationRelation_hom_ext {T : Scheme}
    {f g : T ⟶ cyclicNormalizationRelation n}
    (h₁ : f ≫ cyclicNormalizationRelationFirst n = g ≫ cyclicNormalizationRelationFirst n)
    (h₂ : f ≫ cyclicNormalizationRelationSecond n = g ≫ cyclicNormalizationRelationSecond n) :
    f = g :=
  pullback.hom_ext h₁ h₂

/-- Equality in the closed slice is exactly equality of complete normalized parameters. -/
theorem cyclicNormalizationRelation_iff {T : Scheme}
    (f g : T ⟶ (cyclicAuxiliaryScheme n).left) :
    f ≫ cyclicNormalizationSliceMap n = g ≫ cyclicNormalizationSliceMap n ↔
      cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g := by
  rw [← cancel_mono (cyclicNormalizedSliceInclusion n)]
  simp only [Category.assoc, cyclicNormalizationSliceMap_inclusion,
    cyclicSchemeNormalizedPoint_eq_comp]

end FLT.Mazur.UniversalWeierstrass

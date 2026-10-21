/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterSchemeBaseChange
public import FLT.Mazur.OverPullbackTowerComparison

/-!
# Coherence of character scalar extension in a coefficient tower

Successive coefficient changes agree with direct scalar extension followed by
the canonical pullback comparison, including the actual first projections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.CharacterSchemeBaseChange

open CharacterAlgebraScalarExtension

universe u
variable (A B C M : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [AddCommMonoid M]

/-- Character coefficient maps compose along the specified algebra tower. -/
theorem coeff_tower :
    (coeff B C M).toRingHom.comp (coeff A B M).toRingHom = (coeff A C M).toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro x
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, coeff_single]
    rw [← IsScalarTower.algebraMap_apply A B C]
  · intro x
    simp [coeff]

/-- The composite of the literal coefficient spectrum maps is the direct map. -/
theorem characterTower_baseMap : baseMap B C ≫ baseMap A B = baseMap A C := by
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (IsScalarTower.algebraMap_eq A B C).symm

/-- Successive character recovery retains the direct original projection. -/
@[reassoc] theorem overIso_iterated_fst_fst :
    ((overIso B C M).hom ≫ (Over.pullback (baseMap B C)).map
      (overIso A B M).hom).left ≫
        pullback.fst ((Over.pullback (baseMap A B)).obj (model A M)).hom (baseMap B C) ≫
          pullback.fst (model A M).hom (baseMap A B) =
            Spec.map (CommRingCat.ofHom (coeff A C M).toRingHom) := by
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst_assoc]
  rw [overIso_fst, ← Category.assoc, overIso_fst, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (coeff_tower A B C M)

/-- Direct and successive character recovery agree on the entire pullback source. -/
theorem overIso_tower :
    (overIso A C M).hom ≫
      ((OverPullbackCoherence.towerIso (baseMap A B) (baseMap B C) (baseMap A C)
        (characterTower_baseMap A B C)).app (model A M)).hom =
      (overIso B C M).hom ≫ (Over.pullback (baseMap B C)).map (overIso A B M).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · have h := congrArg (fun k => (overIso A C M).hom.left ≫ k)
        (OverPullbackCoherence.towerIso_fst_fst (baseMap A B) (baseMap B C)
          (baseMap A C) (characterTower_baseMap A B C) (model A M))
      simpa only [Over.comp_left, Category.assoc, Iso.app_hom, Over.pullback_obj_hom] using
        h.trans ((overIso_fst A C M).trans (overIso_iterated_fst_fst A B C M).symm)
    · simp only [Category.assoc]
      change _ ≫ pullback.fst (pullback.snd (model A M).hom (baseMap A B))
        (baseMap B C) ≫ pullback.snd (model A M).hom (baseMap A B) =
          _ ≫ pullback.fst (pullback.snd (model A M).hom (baseMap A B))
            (baseMap B C) ≫ pullback.snd (model A M).hom (baseMap A B)
      rw [pullback.condition, ← Category.assoc, ← Category.assoc]
      exact congrArg (fun k => k ≫ baseMap B C)
        ((Over.w _).trans (Over.w _).symm)
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.CharacterSchemeBaseChange

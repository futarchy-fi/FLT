/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterTranslationBaseChange
public import FLT.Mazur.PolygonNormalizationNodeBaseChange

/-!
# Refinement of translated original normalization and node maps

Every original map into the polygon, composed with a varying translation,
commutes with the actual iterated-pullback comparison. This simultaneously
retains normalization components, nodes and their original branch incidence.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonActionBaseChange
open MonoidalActionSpecialization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T U : Scheme.{u}} (g : T ⟶ Spec (.of K)) (k : U ⟶ T)
local notation "F" => Over.pullback g
local notation "H" => Over.pullback k

/-- Translated original maps commute with refinement on the full schemes. -/
theorem translatedMap_baseChange
    (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) {X : Over (Spec (.of K))} (f : X ⟶ C) :
    (H).map ((F).map f ≫ (translationIso K n hn p q h g c).hom) ≫
        (Over.pullbackComp k g).inv.app C =
      (Over.pullbackComp k g).inv.app X ≫
        ((Over.pullback (k ≫ g)).map f ≫
          (translationIso K n hn p q h (k ≫ g) (parameterBaseChange K n g k c)).hom) := by
  have ht := translation_baseChange K n hn p q h g k c
  rw [← translationIso_hom, ← translationIso_hom] at ht
  rw [Functor.map_comp, Category.assoc, ht, ← Category.assoc]
  have hw := (Over.pullbackComp k g).inv.naturality f
  dsimp only [Functor.comp_map] at hw
  rw [hw, Category.assoc]

/-- The original translated normalization component retains its refinement square. -/
theorem translatedNormalization_baseChange
    (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (i : Fin n) :
    (H).map ((F).map (componentι K n i ≫ p) ≫ (translationIso K n hn p q h g c).hom) ≫
        (Over.pullbackComp k g).inv.app C =
      (Over.pullbackComp k g).inv.app (component K) ≫
        ((Over.pullback (k ≫ g)).map (componentι K n i ≫ p) ≫
          (translationIso K n hn p q h (k ≫ g) (parameterBaseChange K n g k c)).hom) :=
  translatedMap_baseChange K n hn p q h g k c _

/-- The original translated node retains exactly the same refinement square. -/
theorem translatedNode_baseChange
    (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (i : Fin n) :
    (H).map ((F).map (nodeι K n i ≫ q) ≫ (translationIso K n hn p q h g c).hom) ≫
        (Over.pullbackComp k g).inv.app C =
      (Over.pullbackComp k g).inv.app (point K) ≫
        ((Over.pullback (k ≫ g)).map (nodeι K n i ≫ q) ≫
          (translationIso K n hn p q h (k ≫ g) (parameterBaseChange K n g k c)).hom) :=
  translatedMap_baseChange K n hn p q h g k c _

variable (i j : Fin n) (s : point K ⟶ component K)
  (w : s ≫ (componentι K n i ≫ p) = nodeι K n j ≫ q)

include w in
/-- Branch incidence survives refinement of the entire translated original maps. -/
theorem translatedBranch_baseChange
    (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) :
    (H).map ((F).map s) ≫
        (H).map ((F).map (componentι K n i ≫ p) ≫ (translationIso K n hn p q h g c).hom) ≫
          (Over.pullbackComp k g).inv.app C =
      (Over.pullbackComp k g).inv.app (point K) ≫
        ((Over.pullback (k ≫ g)).map (nodeι K n j ≫ q) ≫
          (translationIso K n hn p q h (k ≫ g) (parameterBaseChange K n g k c)).hom) := by
  rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp, w]
  exact translatedNode_baseChange K n hn p q h g k c j

end FLT.Mazur.PolygonParameterTranslation

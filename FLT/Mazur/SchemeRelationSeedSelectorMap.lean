/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSeedSelectorKernel

/-!
# Comparing independently chosen seed representatives

A map of original seeds induces a quotient map even when the two choices
of representatives disagree. Original arrows prove naturality and the
functor laws; the full kernel proves that every such quotient map is monic.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSeedSelector.Data
open SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {S B C E : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  {k : B ⟶ A.left} {l : C ⟶ A.left} {m : E ⟶ A.left}
  (d : Data p q k) (c : Data p q l) (a : B ⟶ C) (ha : a ≫ l = k)
attribute [local irreducible] quotient inclusion projection

/-- Restrict a target projection to the source representatives. -/
def map : d.quotient ⟶ c.quotient := d.inclusion ≫ a ≫ c.projection

include ha in
/-- The two independently chosen representatives give the same quotient morphism. -/
@[reassoc]
theorem projection_map : d.projection ≫ d.map c a = a ≫ c.projection := by
  rw [map, projection_inclusion_assoc]
  apply (cancel_mono c.inclusion).mp
  simp only [Category.assoc, projection_inclusion]
  exact (c.on_arrow d.arrow a (d.rep ≫ a)
    (d.source.trans ha.symm) (by rw [Category.assoc, ha, d.target])).symm

/-- Equality of maps from the quotient is detected on its original seed. -/
theorem hom_ext {T : Scheme.{u}} {x y : d.quotient ⟶ T}
    (h : d.projection ≫ x = d.projection ≫ y) : x = y := by
  have hh := congrArg (fun z ↦ d.inclusion ≫ z) h
  simpa only [inclusion_projection_assoc] using hh

/-- Identity maps do not depend on the chosen representative expressions. -/
theorem map_id : d.map d (𝟙 B) = 𝟙 d.quotient := by
  apply d.hom_ext
  rw [projection_map d d (𝟙 B) (Category.id_comp _), Category.id_comp, Category.comp_id]

include ha in
/-- Comparison maps compose exactly, without compatibility of the selectors. -/
@[reassoc]
theorem map_comp (b : Data p q m) (t : C ⟶ E) (ht : t ≫ m = l) :
    d.map c a ≫ c.map b t = d.map b (a ≫ t) := by
  apply d.hom_ext
  rw [projection_map_assoc d c a ha, projection_map c b t ht,
    projection_map d b (a ≫ t) (by rw [Category.assoc, ht, ha]), Category.assoc]

variable (e : CategoryTheory.EquivalenceRelation p q)

include e ha in
/-- A map of seeds induces a monomorphism of their FULL original quotients. -/
theorem map_mono : Mono (d.map c a) := by
  constructor
  intro Y x y h
  let z := c.kernelLift e (x ≫ d.inclusion ≫ a) (y ≫ d.inclusion ≫ a)
    (by simpa only [map, Category.assoc] using h)
  have hz₁ : (z ≫ SchemeRelationRestriction.arrow p.left q.left l) ≫ p.left =
      (x ≫ d.inclusion) ≫ k := by
    rw [Category.assoc, arrow_fst, ← Category.assoc]
    change (c.kernelLift e _ _ _ ≫ fst p.left q.left l) ≫ l = _
    rw [kernelLift_fst, Category.assoc, Category.assoc, ha, Category.assoc]
  have hz₂ : (z ≫ SchemeRelationRestriction.arrow p.left q.left l) ≫ q.left =
      (y ≫ d.inclusion) ≫ k := by
    rw [Category.assoc, arrow_snd, ← Category.assoc]
    change (c.kernelLift e _ _ _ ≫ snd p.left q.left l) ≫ l = _
    rw [kernelLift_snd, Category.assoc, Category.assoc, ha, Category.assoc]
  apply (cancel_mono d.inclusion).mp
  have hh := d.on_arrow (z ≫ SchemeRelationRestriction.arrow p.left q.left l)
    (x ≫ d.inclusion) (y ≫ d.inclusion) hz₁ hz₂
  simpa only [Category.assoc, inclusion_rep] using hh

/-- Two choices on the same seed yield canonically isomorphic quotient schemes. -/
def comparisonIso (c' : Data p q k) : d.quotient ≅ c'.quotient where
  hom := d.map c' (𝟙 B)
  inv := c'.map d (𝟙 B)
  hom_inv_id := by
    rw [map_comp d c' (𝟙 B) (Category.id_comp _) d (𝟙 B) (Category.id_comp _),
      Category.id_comp, map_id]
  inv_hom_id := by
    rw [map_comp c' d (𝟙 B) (Category.id_comp _) c' (𝟙 B) (Category.id_comp _),
      Category.id_comp, map_id]

end FLT.Mazur.SchemeRelationSeedSelector.Data

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationReanchoring

/-!
# Constructing a quotient scheme from invariant arrow representatives

A section of the first relation endpoint selects an orbit representative.
When its second endpoint is invariant, it is automatically idempotent. Its
fixed scheme constructs the quotient target and a split quotient morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSelectorQuotient
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (r : A.left ⟶ D.left) (hr : r ≫ p.left = 𝟙 A.left)
  (hi : p.left ≫ r ≫ q.left = q.left ≫ r ≫ q.left)

include hr hi in
/-- Invariance forces the chosen representative to be fixed by a second selection. -/
theorem idempotent : (r ≫ q.left) ≫ (r ≫ q.left) = r ≫ q.left := by
  have h := congrArg (fun a ↦ r ≫ a) hi
  simpa only [← Category.assoc, hr, Category.id_comp] using h.symm

/-- The quotient is constructed as a scheme, without a supplied quotient target. -/
def target : Scheme.{u} := equalizer (𝟙 A.left) (r ≫ q.left)

/-- The representative inclusion (q := q) retains the whole fixed scheme structure. -/
def inclusion : target (q := q) r ⟶ A.left := equalizer.ι (𝟙 A.left) (r ≫ q.left)

instance inclusion_mono : Mono (inclusion (q := q) r) :=
  inferInstanceAs (Mono (equalizer.ι (𝟙 A.left) (r ≫ q.left)))

/-- The original source maps to its scheme of representatives. -/
def projection : A.left ⟶ target (q := q) r :=
  equalizer.lift (r ≫ q.left) (by
    simpa only [Category.comp_id] using (idempotent r hr hi).symm)

@[reassoc]
theorem projection_inclusion : projection r hr hi ≫ inclusion (q := q) r = r ≫ q.left :=
  equalizer.lift_ι _ _

@[reassoc]
theorem inclusion_representative : inclusion (q := q) r ≫ r ≫ q.left = inclusion (q := q) r := by
  simpa only [Category.comp_id, inclusion] using (equalizer.condition (𝟙 A.left) (r ≫ q.left)).symm

/-- The constructed quotient has an actual scheme section. -/
@[reassoc]
theorem inclusion_projection :
    inclusion (q := q) r ≫ projection r hr hi = 𝟙 (target (q := q) r) := by
  apply (cancel_mono (inclusion (q := q) r)).mp
  rw [Category.assoc, projection_inclusion, inclusion_representative, Category.id_comp]

/-- Every original relation arrow is coequalized by the constructed projection. -/
theorem condition : p.left ≫ projection r hr hi = q.left ≫ projection r hr hi := by
  apply (cancel_mono (inclusion (q := q) r)).mp
  simpa only [Category.assoc, projection_inclusion] using hi

/-- Every point of the constructed target has a specified original-source lift. -/
instance projection_surjective : Surjective (projection r hr hi) := ⟨fun x ↦
  ⟨inclusion (q := q) r x, congrArg (fun a ↦ a x) (inclusion_projection r hr hi)⟩⟩

/-- Every invariant scheme morphism descends by evaluation on the representatives. -/
def descend {T : Scheme.{u}} (g : A.left ⟶ T) : target (q := q) r ⟶ T := inclusion (q := q) r ≫ g

@[reassoc]
theorem projection_descend {T : Scheme.{u}} (g : A.left ⟶ T)
    (hg : p.left ≫ g = q.left ≫ g) :
    projection r hr hi ≫ descend (q := q) r g = g := by
  rw [descend, projection_inclusion_assoc, ← hg, ← Category.assoc, hr, Category.id_comp]

/-- A map out of the constructed target is determined on the entire original source. -/
theorem descend_unique {T : Scheme.{u}} (g : A.left ⟶ T) (a : target (q := q) r ⟶ T)
    (ha : projection r hr hi ≫ a = g) : a = descend (q := q) r g := by
  rw [descend, ← ha, inclusion_projection_assoc]

/-- The original ground map descends without any change of coefficient base. -/
@[reassoc]
theorem projection_ground : projection r hr hi ≫ inclusion (q := q) r ≫ A.hom = A.hom := by
  exact projection_descend r hr hi A.hom (p.w.trans q.w.symm)

end FLT.Mazur.SchemeRelationSelectorQuotient

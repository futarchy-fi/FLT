/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedEllipticCurve

/-!
# Morphisms of generalized elliptic curves

A morphism consists of a curve map and a smooth-group homomorphism, commuting
with the smooth inclusions and the whole-curve actions. These form a category.
Isomorphisms therefore retain both the group law and the action.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
variable {S : Scheme}

/-- A compatible curve map and smooth-group homomorphism. -/
@[ext]
structure Hom (E F : GeneralizedEllipticCurve S) where
  /-- Map of the underlying relative curves. -/
  curve : E.curve ⟶ F.curve
  /-- Map of the smooth groups. -/
  group : E.group ⟶ F.group
  /-- The smooth map is a group homomorphism. -/
  [isMonHom : IsMonHom group]
  /-- Compatibility with the actual smooth inclusions. -/
  inclusion : E.inclusion ≫ curve = group ≫ F.inclusion
  /-- Equivariance of the whole-curve map. -/
  action : E.act ≫ curve = (group ⊗ₘ curve) ≫ F.act

attribute [instance] Hom.isMonHom

/-- Identity morphism of generalized elliptic curves. -/
def Hom.id (E : GeneralizedEllipticCurve S) : Hom E E where
  curve := 𝟙 E.curve
  group := 𝟙 E.group
  inclusion := by simp
  action := by simp

/-- Composition preserves both the smooth inclusion and the action. -/
def Hom.comp {E F H : GeneralizedEllipticCurve S} (f : Hom E F) (g : Hom F H) : Hom E H where
  curve := f.curve ≫ g.curve
  group := f.group ≫ g.group
  inclusion := by rw [← Category.assoc, f.inclusion, Category.assoc, g.inclusion, Category.assoc]
  action := by
    rw [← Category.assoc, f.action, Category.assoc, g.action,
      ← Category.assoc, ← tensorHom_comp_tensorHom]

instance : Category (GeneralizedEllipticCurve S) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := by ext <;> simp [Hom.id, Hom.comp]
  comp_id _ := by ext <;> simp [Hom.id, Hom.comp]
  assoc _ _ _ := by ext <;> simp [Hom.comp, Category.assoc]

/-- Forget the group/action while retaining the curve over its base. -/
def forgetCurve : GeneralizedEllipticCurve S ⥤ Over S where
  obj E := E.curve
  map f := f.curve

/-- Forget the curve while retaining its smooth-group object over the base. -/
def forgetGroup : GeneralizedEllipticCurve S ⥤ Over S where
  obj E := E.group
  map f := f.group

/-- Compatible morphisms carry identity sections to identity sections. -/
@[reassoc]
theorem Hom.identitySection {E F : GeneralizedEllipticCurve S} (f : E ⟶ F) :
    E.identitySection ≫ f.curve = F.identitySection := by
  rw [GeneralizedEllipticCurve.identitySection, Category.assoc, f.inclusion,
    ← Category.assoc, IsMonHom.one_hom]
  rfl

/-- The chosen smooth-group map is determined by the curve map. -/
theorem Hom.group_eq {E F : GeneralizedEllipticCurve S} (f g : E ⟶ F)
    (h : f.curve = g.curve) : f.group = g.group := by
  have : Mono F.inclusion := by
    dsimp [GeneralizedEllipticCurve.inclusion, curveSmoothInclusion]
    infer_instance
  apply (cancel_mono F.inclusion).mp
  rw [← f.inclusion, ← g.inclusion, h]

instance : (forgetCurve (S := S)).Faithful where
  map_injective {_ _} f g h := Hom.ext h (Hom.group_eq f g h)

/-- Isomorphisms induce isomorphisms of the actual relative curves. -/
def curveIso {E F : GeneralizedEllipticCurve S} (e : E ≅ F) : E.curve ≅ F.curve :=
  forgetCurve.mapIso e

/-- Isomorphisms induce isomorphisms of the smooth groups. -/
def groupIso {E F : GeneralizedEllipticCurve S} (e : E ≅ F) : E.group ≅ F.group :=
  forgetGroup.mapIso e

end FLT.Mazur.GeneralizedEllipticCurve

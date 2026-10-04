/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurvePullback

/-!
# Identity and composition comparisons for pulled-back actions

The canonical natural isomorphisms of actual pullback functors preserve
inclusions and actions. Their components apply to both the curve and group.
This does not yet identify the pulled-back group with the new smooth locus.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.MonoidalActionMap
universe u v w z
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {E : Type w} [Category.{z} E] [MonoidalCategory E]
  {F H : D ⥤ E} [F.LaxMonoidal] [H.LaxMonoidal]
  {G X : D} (a : G ⊗ X ⟶ X)

/-- A monoidal natural transformation preserves a transported action. -/
theorem naturality (τ : F ⟶ H) [NatTrans.IsMonoidal τ] :
    (Functor.LaxMonoidal.μ F G X ≫ F.map a) ≫ τ.app X =
      (τ.app G ⊗ₘ τ.app X) ≫ Functor.LaxMonoidal.μ H G X ≫ H.map a := by
  rw [Category.assoc, τ.naturality, ← Category.assoc, NatTrans.IsMonoidal.tensor]
  simp only [Category.assoc]

/-- A monoidal natural transformation preserves a transported unit. -/
theorem unit_naturality (η : 𝟙_ D ⟶ G) (τ : F ⟶ H) [NatTrans.IsMonoidal τ] :
    (Functor.LaxMonoidal.ε F ≫ F.map η) ≫ τ.app G =
      Functor.LaxMonoidal.ε H ≫ H.map η := by
  rw [Category.assoc, τ.naturality, ← Category.assoc, NatTrans.IsMonoidal.unit]

end FLT.Mazur.MonoidalActionMap

namespace FLT.Mazur.GeneralizedEllipticCurve
open scoped CategoryTheory.Obj
variable {S T U : Scheme} (E : GeneralizedEllipticCurve S)

/-- Canonical comparison for curve pullback along the identity. -/
def pullbackCurveIdIso : E.pullbackCurve (𝟙 S) ≅ E.curve := Over.pullbackId.app E.curve
/-- Canonical comparison for group pullback along the identity. -/
def pullbackGroupIdIso : E.pullbackGroup (𝟙 S) ≅ E.group := Over.pullbackId.app E.group

/-- The identity comparison preserves the smooth-group inclusion. -/
@[reassoc]
theorem pullback_id_inclusion :
    E.pullbackInclusion (𝟙 S) ≫ E.pullbackCurveIdIso.hom =
      E.pullbackGroupIdIso.hom ≫ E.inclusion :=
  Over.pullbackId.hom.naturality E.inclusion

/-- The identity comparison preserves the whole-curve action. -/
@[reassoc]
theorem pullback_id_action :
    E.pullbackAction (𝟙 S) ≫ E.pullbackCurveIdIso.hom =
      (E.pullbackGroupIdIso.hom ⊗ₘ E.pullbackCurveIdIso.hom) ≫ E.act := by
  simpa only [pullbackAction, pullbackCurveIdIso, pullbackGroupIdIso, Iso.app_hom,
    Functor.id_obj, Functor.id_map, Functor.LaxMonoidal.id_μ, Category.id_comp, Category.assoc]
    using MonoidalActionMap.naturality E.act Over.pullbackId.hom

/-- The identity comparison preserves the group identity. -/
theorem pullback_id_one :
    MonObj.one (X := E.pullbackGroup (𝟙 S)) ≫ E.pullbackGroupIdIso.hom =
      MonObj.one (X := E.group) := by
  simpa only [Functor.obj.η_def, pullbackGroupIdIso, Iso.app_hom,
    Functor.id_obj, Functor.id_map, Functor.LaxMonoidal.id_ε, Category.id_comp]
    using MonoidalActionMap.unit_naturality (MonObj.one (X := E.group)) Over.pullbackId.hom

/-- The identity comparison preserves group multiplication. -/
theorem pullback_id_mul :
    MonObj.mul (X := E.pullbackGroup (𝟙 S)) ≫ E.pullbackGroupIdIso.hom =
      (E.pullbackGroupIdIso.hom ⊗ₘ E.pullbackGroupIdIso.hom) ≫ MonObj.mul (X := E.group) := by
  simpa only [Functor.obj.μ_def, pullbackGroupIdIso, Iso.app_hom,
    Functor.id_obj, Functor.id_map, Functor.LaxMonoidal.id_μ, Category.id_comp, Category.assoc]
    using MonoidalActionMap.naturality (MonObj.mul (X := E.group)) Over.pullbackId.hom

variable (g : T ⟶ S) (h : U ⟶ T)

/-- Direct pullback of the curve compares with iterated pullback. -/
def pullbackCurveCompIso : E.pullbackCurve (h ≫ g) ≅ (Over.pullback h).obj (E.pullbackCurve g) :=
  (Over.pullbackComp h g).app E.curve
/-- Direct pullback of the group compares with iterated pullback. -/
def pullbackGroupCompIso : E.pullbackGroup (h ≫ g) ≅ (Over.pullback h).obj (E.pullbackGroup g) :=
  (Over.pullbackComp h g).app E.group

/-- The composition comparison preserves the smooth-group inclusion. -/
@[reassoc]
theorem pullback_comp_inclusion :
    E.pullbackInclusion (h ≫ g) ≫ (E.pullbackCurveCompIso g h).hom =
      (E.pullbackGroupCompIso g h).hom ≫ (Over.pullback h).map (E.pullbackInclusion g) :=
  (Over.pullbackComp h g).hom.naturality E.inclusion

/-- The composition comparison preserves the actual twice-pulled-back action. -/
@[reassoc]
theorem pullback_comp_action :
    E.pullbackAction (h ≫ g) ≫ (E.pullbackCurveCompIso g h).hom =
      ((E.pullbackGroupCompIso g h).hom ⊗ₘ (E.pullbackCurveCompIso g h).hom) ≫
        Functor.LaxMonoidal.μ (Over.pullback h) (E.pullbackGroup g) (E.pullbackCurve g) ≫
          (Over.pullback h).map (E.pullbackAction g) := by
  simpa only [pullbackCurveCompIso, pullbackGroupCompIso, Iso.app_hom,
    Functor.comp_obj, Functor.comp_map, Functor.LaxMonoidal.comp_μ,
    pullbackAction, Functor.map_comp, Category.assoc]
    using MonoidalActionMap.naturality E.act (Over.pullbackComp h g).hom

/-- The composition comparison preserves group identities. -/
theorem pullback_comp_one :
    MonObj.one (X := E.pullbackGroup (h ≫ g)) ≫ (E.pullbackGroupCompIso g h).hom =
      MonObj.one (X := (Over.pullback h).obj (E.pullbackGroup g)) := by
  simpa only [Functor.obj.η_def, pullbackGroupCompIso, Iso.app_hom,
    Functor.comp_obj, Functor.comp_map, Functor.LaxMonoidal.comp_ε,
    Functor.map_comp, Category.assoc]
    using MonoidalActionMap.unit_naturality (MonObj.one (X := E.group))
      (Over.pullbackComp h g).hom

/-- The composition comparison preserves group multiplication. -/
theorem pullback_comp_mul :
    MonObj.mul (X := E.pullbackGroup (h ≫ g)) ≫ (E.pullbackGroupCompIso g h).hom =
      ((E.pullbackGroupCompIso g h).hom ⊗ₘ (E.pullbackGroupCompIso g h).hom) ≫
        MonObj.mul (X := (Over.pullback h).obj (E.pullbackGroup g)) := by
  simpa only [Functor.obj.μ_def, pullbackGroupCompIso, Iso.app_hom,
    Functor.comp_obj, Functor.comp_map, Functor.LaxMonoidal.comp_μ,
    Functor.map_comp, Category.assoc]
    using MonoidalActionMap.naturality (MonObj.mul (X := E.group))
      (Over.pullbackComp h g).hom

/-- Identity comparisons are natural in compatible curve morphisms. -/
theorem pullback_id_natural {F : GeneralizedEllipticCurve S} (f : E ⟶ F) :
    (Over.pullback (𝟙 S)).map f.curve ≫ F.pullbackCurveIdIso.hom =
      E.pullbackCurveIdIso.hom ≫ f.curve := Over.pullbackId.hom.naturality f.curve

/-- Composition comparisons are natural in compatible curve morphisms. -/
theorem pullback_comp_natural {F : GeneralizedEllipticCurve S} (f : E ⟶ F) :
    (Over.pullback (h ≫ g)).map f.curve ≫ (F.pullbackCurveCompIso g h).hom =
      (E.pullbackCurveCompIso g h).hom ≫ (Over.pullback h).map ((Over.pullback g).map f.curve) :=
  (Over.pullbackComp h g).hom.naturality f.curve

end FLT.Mazur.GeneralizedEllipticCurve

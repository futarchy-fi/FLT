/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTripleOverlapMaps
public import FLT.Mazur.SchemeModulePullbackUnits

/-!
# Normalized sections of iterated affine pullbacks

Composition with a specified ring-map equality gives an actual sheaf
isomorphism. On unit sections and their scalar multiples its normalization
is forced by the pullback adjunction. This applies to all six ways to reach
a coordinate of the triple overlap through a pair projection.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineIteratedPullbackSections
open SchemeModulePullbackUnits AffineTripleOverlapMaps
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
variable (M : Z.Modules)

/-- Compose pullbacks and identify the composite with a specified morphism. -/
def compositeIso : (pullback f).obj ((pullback g).obj M) ≅ (pullback k).obj M :=
  (pullbackComp f g).app M ≪≫ (pullbackCongr h).app M

/-- Composite pullback comparison preserves the direct unit section. -/
theorem compositeIso_unit (n : Γ(M, ⊤)) :
    (compositeIso f g k h M).hom.app ⊤
      (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app ⊤
        (((pullbackPushforwardAdjunction g).unit.app M).app ⊤ n)) =
      ((pullbackPushforwardAdjunction k).unit.app M).app ⊤ n := by
  change ((pullbackCongr h).hom.app M).app ⊤
    (((pullbackComp f g).hom.app M).app ⊤ _) = _
  exact (congrArg (((pullbackCongr h).hom.app M).app ⊤) (comp_unit f g M n)).trans
    (congr_unit h M n)

/-- The module-valued affine sections functor has the usual underlying section map. -/
theorem spec_map_apply {A : CommRingCat.{u}} {P Q : (Spec A).Modules}
    (e : P ⟶ Q) (x : moduleSpecΓFunctor.obj P) :
    moduleSpecΓFunctor.map e x = e.app ⊤ x := rfl

/-- The affine unit on coefficient modules, forgetting only its scalar restriction. -/
def specUnit {A B : CommRingCat.{u}} (φ : A ⟶ B) (P : (Spec A).Modules) :
    moduleSpecΓFunctor.obj P →+
      moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj P) :=
  (moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app P) ≫
    (AffineModulePullbackSections.pushforwardSectionsIso φ).hom.app
      ((pullback (Spec.map φ)).obj P)).hom.toAddMonoidHom

/-- The underlying unit is the actual sheaf pullback unit on global sections. -/
theorem specUnit_apply {A B : CommRingCat.{u}} (φ : A ⟶ B) (P : (Spec A).Modules)
    (x : moduleSpecΓFunctor.obj P) :
    specUnit φ P x = ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app P).app ⊤ x := rfl

/-- Naturality of the coefficient unit for arbitrary affine sheaf morphisms. -/
theorem specUnit_naturality {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {P Q : (Spec A).Modules} (e : P ⟶ Q) (x : moduleSpecΓFunctor.obj P) :
    moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map e) (specUnit φ P x) =
      specUnit φ Q (moduleSpecΓFunctor.map e x) := by
  rw [spec_map_apply, specUnit_apply, specUnit_apply, spec_map_apply]
  exact (congrArg (fun a ↦ a.app ⊤ x)
    ((pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality e)).symm

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable (i : A →+* B) (p : B →+* C) (j : A →+* C) (w : p.comp i = j)
variable (N : (Spec (.of A)).Modules)

/-- The affine specialization of the composite pullback comparison. -/
abbrev comparison := compositeIso (Spec.map (CommRingCat.ofHom p))
  (Spec.map (CommRingCat.ofHom i)) (Spec.map (CommRingCat.ofHom j)) (spec_comp i p j w) N

/-- The affine comparison preserves iterated unit sections. -/
theorem comparison_unit (n : moduleSpecΓFunctor.obj N) :
    (comparison i p j w N).hom.app ⊤
      (((pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom p))).unit.app
        ((pullback (Spec.map (CommRingCat.ofHom i))).obj N)).app ⊤
          (((pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom i))).unit.app N).app
            ⊤ n)) =
      ((pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom j))).unit.app N).app ⊤ n :=
  compositeIso_unit _ _ _ _ N n

/-- Normalized lifting of affine coefficient sections. -/
def liftSections :
    moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom i))).obj N) →+
      moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom j))).obj N) :=
  (moduleSpecΓFunctor.map (comparison i p j w N).hom).hom.toAddMonoidHom.comp
    (specUnit (CommRingCat.ofHom p) ((pullback (Spec.map (CommRingCat.ofHom i))).obj N))


end FLT.Mazur.AffineIteratedPullbackSections

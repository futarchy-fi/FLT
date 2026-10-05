/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections

/-!
# Pullback units and the geometric composition comparisons

The actual sheaf pullback comparison maps iterated unit sections to the
unit of the composite. Identity and equality comparisons have the same
normalization. These statements are derived from the adjunction mates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.SchemeModulePullbackUnits
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
/-- Composition of sheaf pullbacks preserves iterated unit sections. -/
theorem comp_unit (M : Z.Modules) (m : Γ(M, ⊤)) :
    ((pullbackComp f g).hom.app M).app ⊤
      (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app ⊤
        (((pullbackPushforwardAdjunction g).unit.app M).app ⊤ m)) =
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app ⊤ m := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have h' := congrArg (fun k ↦ k.app ⊤ m) h
  change (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app ⊤
        (((pullbackPushforwardAdjunction g).unit.app M).app ⊤ m)) =
    ((pullbackComp f g).inv.app M).app ⊤
      (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app ⊤ m) at h'
  erw [h']
  exact congrArg (fun k : (pullback (f ≫ g)).obj M ⟶ (pullback (f ≫ g)).obj M ↦
    k.app ⊤ (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app ⊤ m))
      ((pullbackComp f g).app M).inv_hom_id
/-- The identity pullback comparison cancels the unit section. -/
theorem id_unit (M : X.Modules) (m : Γ(M, ⊤)) :
    ((pullbackId X).hom.app M).app ⊤
      (((pullbackPushforwardAdjunction (𝟙 X)).unit.app M).app ⊤ m) = m := by
  have h := unit_conjugateEquiv Adjunction.id
    (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom M
  rw [conjugateEquiv_pullbackId_hom] at h
  exact (congrArg (fun k ↦ k.app ⊤ m) h).symm

/-- Equality of scheme morphisms identifies their unit sections. -/
theorem congr_unit {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) (m : Γ(M, ⊤)) :
    ((pullbackCongr h).hom.app M).app ⊤
      (((pullbackPushforwardAdjunction f).unit.app M).app ⊤ m) =
      ((pullbackPushforwardAdjunction g).unit.app M).app ⊤ m := by
  subst g
  rfl

/-- Pulling back along a retraction identifies the iterated pullback with the original sheaf. -/
def retractIso (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) (M : X.Modules) :
    (pullback f).obj ((pullback g).obj M) ≅ M :=
  (pullbackComp f g).app M ≪≫ (pullbackCongr h).app M ≪≫ (pullbackId X).app M

/-- The retraction comparison recovers the original section from its two unit pullbacks. -/
theorem retractIso_unit (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (M : X.Modules) (m : Γ(M, ⊤)) :
    (retractIso f g h M).hom.app ⊤
      (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app ⊤
        (((pullbackPushforwardAdjunction g).unit.app M).app ⊤ m)) = m := by
  change ((pullbackId X).hom.app M).app ⊤
    (((pullbackCongr h).hom.app M).app ⊤
      (((pullbackComp f g).hom.app M).app ⊤ _)) = _
  exact (congrArg (fun z ↦ ((pullbackId X).hom.app M).app ⊤
    (((pullbackCongr h).hom.app M).app ⊤ z)) (comp_unit f g M m)).trans
      ((congrArg (fun z ↦ ((pullbackId X).hom.app M).app ⊤ z)
        (congr_unit h M m)).trans (id_unit M m))

section Spec
variable {A B : CommRingCat.{u}} (φ : A ⟶ B) (M : (Spec A).Modules)

/-- The actual unit section map is semilinear for the affine ring homomorphism. -/
theorem spec_unit_smul (a : A) (m : moduleSpecΓFunctor.obj M) :
    ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ (a • m) =
      φ a • (show moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M) from
        ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m) := by
  let l := moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
    (AffineModulePullbackSections.pushforwardSectionsIso φ).hom.app
      ((pullback (Spec.map φ)).obj M)
  exact l.hom.map_smul a m

/-- A retraction evaluates a pulled-back multiple by applying the return ring map. -/
theorem spec_retract_smul_unit (ψ : B ⟶ A)
    (h : Spec.map ψ ≫ Spec.map φ = 𝟙 (Spec A)) (b : B)
    (m : moduleSpecΓFunctor.obj M) :
    (retractIso (Spec.map ψ) (Spec.map φ) h M).hom.app ⊤
      (((pullbackPushforwardAdjunction (Spec.map ψ)).unit.app
        ((pullback (Spec.map φ)).obj M)).app ⊤
          (b • (show moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M) from
            ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m))) =
      ψ b • m := by
  have hs := spec_unit_smul ψ ((pullback (Spec.map φ)).obj M) b
    (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m)
  let q := moduleSpecΓFunctor.map (retractIso (Spec.map ψ) (Spec.map φ) h M).hom
  change q _ = _
  exact (congrArg q hs).trans ((q.hom.map_smul _ _).trans
    (congrArg (fun z : moduleSpecΓFunctor.obj M ↦ ψ b • z)
      (retractIso_unit (Spec.map ψ) (Spec.map φ) h M m)))

end Spec
end FLT.Mazur.SchemeModulePullbackUnits

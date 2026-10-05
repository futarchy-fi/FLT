/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIteratedPullbackSections

/-!
# Coefficient units followed by a sheaf map

These identities keep the target sheaf abstract, so specializing them to
iterated pullbacks does not unfold the construction of those sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B : CommRingCat.{u}} (φ : A ⟶ B)
variable (P : (Spec A).Modules) {Q : (Spec B).Modules}

/-- A coefficient pullback unit followed by an arbitrary sheaf map. -/
def mappedUnit (e : (pullback (Spec.map φ)).obj P ⟶ Q) :
    moduleSpecΓFunctor.obj P →+ moduleSpecΓFunctor.obj Q :=
  (moduleSpecΓFunctor.map e).hom.toAddMonoidHom.comp (specUnit φ P)

/-- Evaluation uses the actual global-section map and pullback unit. -/
theorem mappedUnit_apply (e : (pullback (Spec.map φ)).obj P ⟶ Q)
    (x : moduleSpecΓFunctor.obj P) :
    mappedUnit φ P e x =
      e.app ⊤ (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app P).app ⊤ x) := rfl

/-- The coefficient pullback unit is semilinear over the affine ring map. -/
theorem specUnit_smul (a : A) (x : moduleSpecΓFunctor.obj P) :
    specUnit φ P (a • x) = φ a • specUnit φ P x :=
  SchemeModulePullbackUnits.spec_unit_smul φ P a x

/-- Following a pullback unit by a sheaf map preserves its scalar law. -/
theorem mappedUnit_smul (e : (pullback (Spec.map φ)).obj P ⟶ Q)
    (a : A) (x : moduleSpecΓFunctor.obj P) :
    mappedUnit φ P e (a • x) = φ a • mappedUnit φ P e x := by
  change moduleSpecΓFunctor.map e (specUnit φ P (a • x)) = _
  rw [specUnit_smul]
  exact (moduleSpecΓFunctor.map e).hom.map_smul _ _

/-- Conjugated pullback maps intertwine the normalized coefficient units. -/
theorem mappedUnit_map {P' : (Spec A).Modules} {Q' : (Spec B).Modules}
    (c : (pullback (Spec.map φ)).obj P ≅ Q)
    (c' : (pullback (Spec.map φ)).obj P' ≅ Q') (e : P ⟶ P')
    (x : moduleSpecΓFunctor.obj P) :
    moduleSpecΓFunctor.map (c.inv ≫ (pullback (Spec.map φ)).map e ≫ c'.hom)
      (mappedUnit φ P c.hom x) =
        mappedUnit φ P' c'.hom (moduleSpecΓFunctor.map e x) := by
  have hc : c.hom ≫ (c.inv ≫ (pullback (Spec.map φ)).map e ≫ c'.hom) =
      (pullback (Spec.map φ)).map e ≫ c'.hom := by
    simp only [Iso.hom_inv_id_assoc]
  have hm := congrArg (fun a ↦ moduleSpecΓFunctor.map a (specUnit φ P x)) hc
  simp only [Functor.map_comp, ModuleCat.comp_apply] at hm
  exact hm.trans (congrArg (moduleSpecΓFunctor.map c'.hom) (specUnit_naturality φ e x))

/-- The scalar law over unbundled rings, with the sheaf objects kept abstract. -/
theorem mappedUnit_ringHom_smul {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : (Spec (.of R)).Modules) {N : (Spec (.of S)).Modules}
    (e : (pullback (Spec.map (CommRingCat.ofHom f))).obj M ⟶ N)
    (r : R) (x : moduleSpecΓFunctor.obj M) :
    mappedUnit (CommRingCat.ofHom f) M e (r • x) =
      f r • mappedUnit (CommRingCat.ofHom f) M e x := by
  exact mappedUnit_smul (CommRingCat.ofHom f) M e r x

end FLT.Mazur.AffineIteratedPullbackSections

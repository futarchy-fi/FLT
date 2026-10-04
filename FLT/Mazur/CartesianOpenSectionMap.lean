/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenCartesianSections

/-!
# The canonical cartesian section map over the base

The adjunction unit defines the base-linear tensor comparison on every open.
Affineness is needed only to prove that this map is an isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.CartesianOpenSectionMap
open OpenModuleSectionScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme.{u}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) (U : X.Opens)

/-- The pullback unit on an open, linear over the structural base ring. -/
def unitMap : openSections f M U ⟶
    (ModuleCat.restrictScalars g.appTop.hom).obj
      (openSections q ((pullback p).obj M) (p ⁻¹ᵁ U)) :=
  ModuleCat.ofHom (X := openSections f M U)
    (Y := (ModuleCat.restrictScalars g.appTop.hom).obj
      (openSections q ((pullback p).obj M) (p ⁻¹ᵁ U)))
    ({ toFun := ((pullbackPushforwardAdjunction p).unit.app M).app U
       map_add' := map_add (((pullbackPushforwardAdjunction p).unit.app M).app U).hom
       map_smul' := fun r m ↦ by
         change ((pullbackPushforwardAdjunction p).unit.app M).app U
           (X.presheaf.map U.leTop.op (f.appTop r) • m) =
           P.presheaf.map (p ⁻¹ᵁ U).leTop.op (q.appTop (g.appTop r)) •
             (show Γ((pullback p).obj M, p ⁻¹ᵁ U) from
               ((pullbackPushforwardAdjunction p).unit.app M).app U m)
         rw [Hom.app_smul]
         change p.app U (X.presheaf.map U.leTop.op (f.appTop r)) •
           (show Γ((pullback p).obj M, p ⁻¹ᵁ U) from
             ((pullbackPushforwardAdjunction p).unit.app M).app U m) = _
         have hw := congrArg (fun a : P ⟶ S ↦ a.appTop r) h.w
         change p.appTop (f.appTop r) = q.appTop (g.appTop r) at hw
         rw [← hw]
         congr 1
         exact (congrArg (fun k ↦ k (f.appTop r)) (p.naturality U.leTop.op)) } :
      openSections f M U →ₗ[Γ(S, ⊤)]
        (ModuleCat.restrictScalars g.appTop.hom).obj
          (openSections q ((pullback p).obj M) (p ⁻¹ᵁ U)))

/-- Canonical base extension of the actual adjunction-unit section map. -/
def comparison :
    (ModuleCat.extendScalars g.appTop.hom).obj (openSections f M U) ⟶
      openSections q ((pullback p).obj M) (p ⁻¹ᵁ U) :=
  ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).symm (unitMap h M U)

/-- Unit tensors map to the actual pullback unit. -/
lemma comparison_one_tmul (m : openSections f M U) :
    comparison h M U ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) =
      ((pullbackPushforwardAdjunction p).unit.app M).app U m := by
  exact congrArg (fun k ↦ k m)
    (((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).apply_symm_apply
      (unitMap h M U))

/-- Pure tensors map to the pulled-back section multiplied by the base scalar. -/
lemma comparison_tmul (b : Γ(T, ⊤)) (m : openSections f M U) :
    comparison h M U (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) =
      b • (show openSections q ((pullback p).obj M) (p ⁻¹ᵁ U) from
        ((pullbackPushforwardAdjunction p).unit.app M).app U m) := by
  have hs := (comparison h M U).hom.map_smul b
    (show (ModuleCat.extendScalars g.appTop.hom).obj (openSections f M U) from
      (1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m)
  have ht : b • ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m :
      (ModuleCat.extendScalars g.appTop.hom).obj (openSections f M U)) =
      b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m := by
    exact (ModuleCat.ExtendScalars.smul_tmul g.appTop.hom b 1 m).trans
      (congrArg (fun a : Γ(T, ⊤) ↦ a ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) (mul_one b))
  rw [ht, comparison_one_tmul] at hs
  exact hs

/-- The base comparison equals the comparison over the ring of the open itself. -/
lemma comparison_tmul_eq (b : Γ(T, ⊤)) (m : openSections f M U) :
    comparison h M U (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) =
      ModuleSectionBaseChange.comparison p M U
        ((P.presheaf.map (p ⁻¹ᵁ U).leTop.op (q.appTop b))
          ⊗ₜ[Γ(X, U),(p.app U).hom] m) := by
  rw [comparison_tmul, ModuleSectionBaseChange.comparison_tmul]
  rfl

/-- The canonical base comparison commutes with restrictions on pure tensors. -/
lemma comparison_restrict {U V : X.Opens} (i : U ⟶ V)
    (b : Γ(T, ⊤)) (m : openSections f M V) :
    ((pullback p).obj M).presheaf.map ((TopologicalSpace.Opens.map p.base).map i).op
      (comparison h M V (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m)) =
    comparison h M U (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] (M.presheaf.map i.op m)) := by
  rw [comparison_tmul_eq, ModuleSectionBaseChange.comparison_restrict,
    comparison_tmul_eq, ← Functor.map_comp_apply]
  rfl

/-- On affine opens the canonical map is the transported affine comparison. -/
lemma comparison_eq [IsAffine T] [IsAffine S] [M.IsQuasicoherent]
    (hU : IsAffineOpen U) :
    comparison h M U = (AffineOpenCartesianSections.sectionsIso h M U hU).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  rw [comparison_one_tmul, AffineOpenCartesianSections.sectionsIso_tmul, one_smul]

/-- The canonical comparison is invertible on an affine open of any scheme. -/
lemma comparison_isIso [IsAffine T] [IsAffine S] [M.IsQuasicoherent]
    (hU : IsAffineOpen U) : IsIso (comparison h M U) := by
  rw [comparison_eq h M U hU]
  infer_instance

end FLT.Mazur.CartesianOpenSectionMap

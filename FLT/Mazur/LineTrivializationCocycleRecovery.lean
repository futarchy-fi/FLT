/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTrivializationCocycle
public import FLT.Mazur.ModuleUnitCocyclePullback

/-!
# Recovery from the cocycle of a line trivialization

The sheaf glued from the genuine transition ratios is isomorphic to the
original line sheaf. Its chart comparisons use the prescribed trivializations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.ModuleSheafMorphismGluing

namespace FLT.Mazur.FCurve

universe u

variable {X : Scheme.{u}} {L : X.Modules}

/-- Ambient coordinates agree with the prescribed trivialization on image opens. -/
theorem lineTrivializationCoordinates_image {U : X.Opens}
    (e : L.restrict U.ι ≅ structureModule U.toScheme) (W : U.toScheme.Opens)
    (s : Γ(L, U.ι ''ᵁ W)) :
    lineTrivializationCoordinates e (U.ι_image_le W) s = e.hom.app W s := by
  have h : (overFunctorEquiv U).inv.app L ≫
      (overEquiv U).functor.map (lineTrivializationSlice e).hom ≫
        (overFunctorEquiv U).hom.app (structureModule X) =
          e.hom ≫ (restrictUnitIso U.ι).inv := by
    simp only [lineTrivializationSlice, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id_app]
    rfl
  have hh := congrArg (fun a ↦ a.app W s) h
  change lineTrivializationCoordinates e (U.ι_image_le W) s =
    (U.ι.appIso W).inv (e.hom.app W s) at hh
  rw [Scheme.Opens.ι_appIso] at hh
  exact hh

variable {ι : Type u} {U : ι → X.Opens}
  (e : ∀ i, L.restrict (U i).ι ≅ structureModule (U i).toScheme)

/-- The local recovery is the cocycle evaluation followed by the original inverse chart. -/
def lineTrivializationCocycleLocalIso (i : ι) :
    (lineTrivializationCocycle e).sheaf.restrict (U i).ι ≅ L.restrict (U i).ι :=
  (lineTrivializationCocycle e).restrictIso i ≪≫ (e i).symm

/-- The local recovery has the expected expression on every ambient subopen. -/
theorem lineTrivializationCocycleLocalIso_app (i : ι) (V : X.Opens) (h : V ≤ U i)
    (s : (lineTrivializationCocycle e).sections V) :
    localApp ((restrictionEquiv (U i)).symm
      (lineTrivializationCocycleLocalIso e i).hom) h s =
        (lineTrivializationCoordinates (e i) h).symm
          ((lineTrivializationCocycle e).evaluate i h s) := by
  obtain ⟨W, rfl⟩ : ∃ W : (U i).toScheme.Opens, (U i).ι ''ᵁ W = V :=
    ⟨(U i).ι ⁻¹ᵁ V, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr h]⟩
  have hh := congrArg (fun a ↦ a.app W s)
    ((restrictionEquiv (U i)).apply_symm_apply (lineTrivializationCocycleLocalIso e i).hom)
  change localApp ((restrictionEquiv (U i)).symm
    (lineTrivializationCocycleLocalIso e i).hom) h s =
      (lineTrivializationCocycleLocalIso e i).hom.app W s at hh
  apply (lineTrivializationCoordinates (e i) h).injective
  rw [LinearEquiv.apply_symm_apply, hh, lineTrivializationCoordinates_image]
  change (e i).hom.app W ((e i).inv.app W _) = _
  exact congrArg (fun a ↦ a.app W ((lineTrivializationCocycle e).evaluate i h s))
    (e i).inv_hom_id

/-- The actual local recovery maps agree on every overlap. -/
theorem lineTrivializationCocycleLocalIso_compatible :
    Compatible U (fun i ↦ (restrictionEquiv (U i)).symm
      (lineTrivializationCocycleLocalIso e i).hom) := by
  intro i j V hi hj
  ext s
  rw [lineTrivializationCocycleLocalIso_app, lineTrivializationCocycleLocalIso_app]
  apply (lineTrivializationCoordinates (e i) hi).injective
  rw [LinearEquiv.apply_symm_apply,
    lineTrivializationCocycle_coordinates e i j V hi hj, LinearEquiv.apply_symm_apply]
  exact (lineTrivializationCocycle e).transition i j hi hj s

/-- Gluing the genuine transition cocycle recovers the original line sheaf. -/
def lineTrivializationCocycleIso (hU : iSup U = ⊤) :
    (lineTrivializationCocycle e).sheaf ≅ L :=
  glueLocalIso U hU (lineTrivializationCocycleLocalIso e)
    (lineTrivializationCocycleLocalIso_compatible e)

end FLT.Mazur.FCurve

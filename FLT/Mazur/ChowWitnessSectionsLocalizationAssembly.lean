/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessAffinePieceCoordinates
public import FLT.Mazur.ClosedPushforwardRestriction

/-!
# Localization of Chow witness sections

The affine-base equalizer calculation transports to the actual direct image on
an affine target open, including the zeroth tensor power.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve CoherentDevissage

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.Chow

section Transport

variable {Y Z : Scheme} {R : Type} [CommRing R]

/-- Pushforward and restriction of the base scalars give the same section module. -/
def pushforwardBaseSectionsEquiv (M : Y.Modules) (g : Y ⟶ Z)
    (ρ : R →+* Γ(Z, ⊤)) (U : Z.Opens) :
    baseSections ((pushforward g).obj M) ρ U ≃ₗ[R]
      baseSections M (g.appTop.hom.comp ρ) (g ⁻¹ᵁ U) where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r s := by
    change g.app U (Z.presheaf.map U.leTop.op (ρ r)) • (show Γ(M, g ⁻¹ᵁ U) from s) =
      Y.presheaf.map (g ⁻¹ᵁ U).leTop.op (g.appTop (ρ r)) •
        (show Γ(M, g ⁻¹ᵁ U) from s)
    congr 1
    exact congr($(g.naturality U.leTop.op) (ρ r))

/-- Ambient section coordinates for the restriction to an open subscheme. -/
def ambientBaseSectionsEquiv (N : Z.Modules) (V : Z.Opens) (U : V.toScheme.Opens) :
    baseSections (N.restrict V.ι) V.topIso.inv.hom U ≃ₗ[Γ(Z, V)]
      (ModuleCat.restrictScalars
        (Z.presheaf.map (homOfLE (V.ι_image_le U)).op).hom).obj
          (N.val.obj (op (V.ι ''ᵁ U))) where
  toFun := (N.restrictAppIso V.ι U).hom
  invFun := (N.restrictAppIso V.ι U).inv
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := map_add _
  map_smul' r s := by
    change (V.ι.appIso U).inv
      (V.toScheme.presheaf.map U.leTop.op (V.topIso.inv r)) •
        (show Γ(N, V.ι ''ᵁ U) from s) = _
    rw [Scheme.Opens.ι_appIso]
    change Z.presheaf.map _ (Z.presheaf.map _ r) • _ = _
    simp only [← Functor.map_comp_apply]
    rfl

end Transport

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The affine spectrum scalar map is the original structural scalar map. -/
lemma graphPowerBaseScalars_eq (V : X.Opens) (hV : IsAffineOpen V) :
    graphPowerBaseScalars f V hV =
      (graphClosureπ f ∣_ V).appTop.hom.comp V.topIso.inv.hom := by
  unfold graphPowerBaseScalars
  rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, CommRingCat.hom_comp]

/-- Base-linear sections on the restricted Chow scheme are ambient direct-image sections. -/
def graphAmbientBaseEquiv (n : ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (U : V.toScheme.Opens) :
    baseSections (graphPowerOver f n V) (graphPowerBaseScalars f V hV)
      ((graphClosureπ f ∣_ V) ⁻¹ᵁ U) ≃ₗ[Γ(X, V)]
    (ModuleCat.restrictScalars
      (X.presheaf.map (homOfLE (V.ι_image_le U)).op).hom).obj
        ((graphPowerPushforward f n).val.obj (op (V.ι ''ᵁ U))) := by
  let e := (pushforwardBaseSectionsEquiv (graphPowerOver f n V)
    (graphClosureπ f ∣_ V) V.topIso.inv.hom U).symm.trans
      ((baseSectionsIsoEquiv ((closedPushforwardRestriction (graphClosureπ f) V).app
        (graphLineBundlePower f n)).symm V.topIso.inv.hom U).trans
          (ambientBaseSectionsEquiv (graphPowerPushforward f n) V U))
  exact { e.toAddEquiv with
    map_smul' := fun r s ↦ by
      change e (((graphClosureπ f ⁻¹ᵁ V).toScheme.presheaf.map
        ((graphClosureπ f ∣_ V) ⁻¹ᵁ U).leTop.op).hom (graphPowerBaseScalars f V hV r) •
          (show Γ(graphPowerOver f n V, (graphClosureπ f ∣_ V) ⁻¹ᵁ U) from s)) = _
      rw [graphPowerBaseScalars_eq]
      exact e.map_smul r s }

/-- Coordinates over a target subopen retain the restriction of its scalar ring. -/
def graphOriginalBaseEquiv (n : ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (T : X.Opens) (hT : T ≤ V) :
    baseSections (graphPowerOver f n V) (graphPowerBaseScalars f V hV)
      ((graphClosureπ f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ T)) ≃ₗ[Γ(X, V)]
    (ModuleCat.restrictScalars (X.presheaf.map (homOfLE hT).op).hom).obj
      ((graphPowerPushforward f n).val.obj (op T)) := by
  let e := graphAmbientBaseEquiv f n V hV (V.ι ⁻¹ᵁ T)
  have h : V.ι ''ᵁ (V.ι ⁻¹ᵁ T) = T := by
    simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hT]
  let d := (graphPowerPushforward f n).presheaf.mapIso (eqToIso h.symm).op
  exact { e.toAddEquiv.trans d.addCommGroupIsoToAddEquiv with
    map_smul' := fun r s ↦ by
      change d.hom (e (r • s)) = _
      rw [e.map_smul]
      change (graphPowerPushforward f n).presheaf.map (eqToHom h.symm).op
        ((X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ T))).op r) •
          (show Γ(graphPowerPushforward f n, V.ι ''ᵁ (V.ι ⁻¹ᵁ T)) from e s)) = _
      rw [(graphPowerPushforward f n).map_smul]
      congr 1
      simp only [← Functor.map_comp_apply, ← op_comp]
      rfl }

set_option maxHeartbeats 600000 in
-- The coefficient square unfolds nested pushforward and restriction equivalences.
/-- The actual Chow coefficient restriction is localization on every affine target open. -/
theorem graphPowerRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (graphPowerRestriction f n V r) := by
  let M := graphPowerOver f n V
  let ρ := graphPowerBaseScalars f V hV
  let g := graphClosureπ f ∣_ V
  let p := baseRestriction M ρ
    ((Opens.map g.base).map ((Opens.map V.ι.base).map (homOfLE (X.basicOpen_le r)))).le
  have hp : IsLocalizedModule (.powers r) p := by
    apply (baseRestriction_isLocalized_congr M ρ r _ _ ?_ ?_).mp
      (graphPowerOver_baseRestriction_isLocalized f n V hV r)
    · simp only [Scheme.Hom.comp_preimage, IsAffineOpen.isoSpec_hom,
        Scheme.Opens.toSpecΓ_preimage_basicOpen]
      rfl
    · change (⊤ : (graphClosureπ f ⁻¹ᵁ V).toScheme.Opens) = g ⁻¹ᵁ V.ι ⁻¹ᵁ V
      simp
  let e : baseSections M ρ (g ⁻¹ᵁ V.ι ⁻¹ᵁ V) ≃ₗ[Γ(X, V)]
      Γ(graphPowerPushforward f n, V) :=
    (graphOriginalBaseEquiv f n V hV V le_rfl).trans
      (ModuleCat.restrictScalarsId'App (R := Γ(X, V)) _ (by
        change (X.presheaf.map (𝟙 (op V))).hom = RingHom.id _
        rw [X.presheaf.map_id]; rfl)
        (ModuleCat.of Γ(X, V) Γ(graphPowerPushforward f n, V))).toLinearEquiv
  let b := graphOriginalBaseEquiv f n V hV (X.basicOpen r) (X.basicOpen_le r)
  apply (IsLocalizedModule.comp_iff_of_bijective_right (.powers r) e.toLinearMap e.bijective).mp
  have hsquare : (graphPowerRestriction f n V r).comp e.toLinearMap =
      b.toLinearMap.comp p := by
    ext s
    have htop : V.ι ''ᵁ (V.ι ⁻¹ᵁ V) = V := by simp
    have hr : V.ι ''ᵁ (V.ι ⁻¹ᵁ X.basicOpen r) = X.basicOpen r := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr (X.basicOpen_le r)]
    change (graphPowerPushforward f n).presheaf.map (homOfLE (X.basicOpen_le r)).op
      ((graphPowerPushforward f n).presheaf.map (eqToHom htop.symm).op
        ((graphLineBundlePower f n).presheaf.map
          (eqToHom (image_morphismRestrict_preimage (graphClosureπ f) V (V.ι ⁻¹ᵁ V)).symm).op s)) =
      (graphPowerPushforward f n).presheaf.map (eqToHom hr.symm).op
        ((graphLineBundlePower f n).presheaf.map
          (eqToHom (image_morphismRestrict_preimage (graphClosureπ f) V
            (V.ι ⁻¹ᵁ X.basicOpen r)).symm).op
          (M.presheaf.map ((Opens.map g.base).map
            ((Opens.map V.ι.base).map (homOfLE (X.basicOpen_le r)))).op s))
    simp only [graphPowerPushforward, pushforward_obj_presheaf_map, M, graphPowerOver,
      restrict_map]
    erw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply]
    rfl
  rw [hsquare]
  exact IsLocalizedModule.of_linearEquiv (.powers r) p b

end FLT.Mazur.Chow

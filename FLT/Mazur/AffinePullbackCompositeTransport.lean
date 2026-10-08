/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackNormalization
public import FLT.Mazur.AffineRefinementComposition

/-!
# Objectwise composition with endpoint transport

Normalize a composite pullback after changing its endpoint by equality.
The affine specialization connects ring composition charts to geometric refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Endpoint transport composes with the objectwise pullback comparison. -/
@[reassoc]
theorem compositeIso_trans {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (k k' : U ⟶ W) (h : f ≫ g = k) (e : k = k') (M : W.Modules) :
    (compositeIso f g k h M).hom ≫ (pullbackCongr e).hom.app M =
      (compositeIso f g k' (h.trans e) M).hom := by
  subst k'
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]

/-- The named square chart agrees with the objectwise pullback comparison. -/
theorem schemeCompositionChart_eq {U V W : Scheme.{u}}
    (f : U ⟶ V) (g : V ⟶ W) (k : U ⟶ W) (h : f ≫ g = k) (M : W.Modules) :
    SchemePullbackSquare.compositionChart f g k h M = compositeIso f g k h M := rfl

/-- The affine ring-composition chart is the objectwise scheme comparison. -/
theorem affineCompositionChart_eq {R A B : CommRingCat.{u}}
    (a : R ⟶ A) (α : A ⟶ B) (M : (Spec R).Modules) :
    AffineRefinementPullback.compositionChart a α M =
      compositeIso (Spec.map α) (Spec.map a) (Spec.map (a ≫ α))
        (Spec.map_comp a α).symm M := by
  exact schemeCompositionChart_eq _ _ _ _ M

/-- An affine chart followed by endpoint transport normalizes the whole path. -/
@[reassoc]
theorem affineCompositionChart_trans {R A B : CommRingCat.{u}}
    (a : R ⟶ A) (α : A ⟶ B) (a' : R ⟶ B) (h : a ≫ α = a') (M : (Spec R).Modules) :
    (AffineRefinementPullback.compositionChart a α M).hom ≫
        (pullbackCongr (congrArg Spec.map h)).hom.app M =
      (compositeIso (Spec.map α) (Spec.map a) (Spec.map a')
        ((Spec.map_comp a α).symm.trans (congrArg Spec.map h)) M).hom := by
  rw [affineCompositionChart_eq]
  exact compositeIso_trans _ _ _ _ _ _ M

end FLT.Mazur.AffineIteratedPullbackSections

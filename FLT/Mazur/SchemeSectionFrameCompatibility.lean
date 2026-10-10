/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeSectionFrameNormalization
public import FLT.Mazur.SchemeIndependentCanonicalOverlap

/-!
# Compatible section frames on independent member squares

Preservation of local rigidifications by canonical total-space overlap maps
implies agreement of the original base frames, including structural unit maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
open SheafPullbackPathComparison SchemeIndependentCanonicalOverlap
open FCurve FCurve.LineSheafSectionRigidity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y₁ Y₂ Z S T₁ T₂ U : Scheme.{u}}
variable (s : S ⟶ X) (t₁ : T₁ ⟶ Y₁) (t₂ : T₂ ⟶ Y₂) (r : U ⟶ Z)
variable (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (b₁ : T₁ ⟶ S) (b₂ : T₂ ⟶ S)
variable (q₁ : Z ⟶ Y₁) (q₂ : Z ⟶ Y₂) (c₁ : U ⟶ T₁) (c₂ : U ⟶ T₂)
variable (w₁ : t₁ ≫ p₁ = b₁ ≫ s) (w₂ : t₂ ≫ p₂ = b₂ ≫ s)
variable (v₁ : r ≫ q₁ = c₁ ≫ t₁) (v₂ : r ≫ q₂ = c₂ ≫ t₂)
variable (k : Z ⟶ X) (d : U ⟶ S) (hp₁ : q₁ ≫ p₁ = k) (hp₂ : q₂ ≫ p₂ = k)
variable (hb₁ : c₁ ≫ b₁ = d) (hb₂ : c₂ ≫ b₂ = d)

/-- Canonical total-space preservation forces the original base-frame agreement. -/
theorem sectionFrames_pair (A : X.Modules)
    (ρ₁ : (pullback t₁).obj ((pullback p₁).obj A) ≅ structureModule T₁)
    (ρ₂ : (pullback t₂).obj ((pullback p₂).obj A) ≅ structureModule T₂)
    (h : (pullback r).map (overlap p₁ p₂ q₁ q₂ k hp₁ hp₂ A).hom ≫
        (squareIso t₂ r q₂ c₂ v₂).hom.app ((pullback p₂).obj A) ≫
        (pullback c₂).map ρ₂.hom ≫ (modulePullbackUnitIso c₂).hom =
      (squareIso t₁ r q₁ c₁ v₁).hom.app ((pullback p₁).obj A) ≫
        (pullback c₁).map ρ₁.hom ≫ (modulePullbackUnitIso c₁).hom) :
    (overlap b₁ b₂ c₁ c₂ d hb₁ hb₂ ((pullback s).obj A)).hom ≫
        (pullback c₂).map ((squareIso s t₂ p₂ b₂ w₂).inv.app A ≫ ρ₂.hom) ≫
        (modulePullbackUnitIso c₂).hom =
      (pullback c₁).map ((squareIso s t₁ p₁ b₁ w₁).inv.app A ≫ ρ₁.hom) ≫
        (modulePullbackUnitIso c₁).hom := by
  have wv : r ≫ k = d ≫ s := by
    rw [← hp₁, ← Category.assoc, v₁, Category.assoc, w₁, ← Category.assoc, hb₁]
  apply (cancel_epi ((comparison c₁ b₁ d hb₁).inv.app ((pullback s).obj A))).mp
  simp only [overlap, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  apply (cancel_epi ((squareIso s r k d wv).hom.app A)).mp
  rw [← sectionFrame_normalize s t₂ r p₂ b₂ q₂ c₂ w₂ v₂ k d hp₂ hb₂ wv,
    ← sectionFrame_normalize s t₁ r p₁ b₁ q₁ c₁ w₁ v₁ k d hp₁ hb₁ wv]
  apply (cancel_epi ((pullback r).map ((comparison q₁ p₁ k hp₁).hom.app A))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simpa only [overlap, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc] using h

end FLT.Mazur.SchemePullbackSquare

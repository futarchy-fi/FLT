/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackSectionReconstruction
public import FLT.Mazur.AffineNamedRefinementReconstruction

/-!
# Named affine reconstruction restricted to a section

A section of the refined affine cover recovers the original reconstruction
along the retained covering lift. The proof is independent of the chosen
sheaves and can be specialized without expanding their constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineNamedRefinementReconstruction
open SheafPullbackPathComparison SchemeModulePullbackUnits AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}} {Y : Scheme.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ)

/-- The named affine reconstruction is the named reconstruction of its scheme square. -/
lemma chart_eq_scheme (c : Spec S ⟶ Y) (c' : Spec S' ⟶ Y)
    (hc : Spec.map b ≫ c = c') {A : (Spec R).Modules} {M : Y.Modules}
    (e : (pullback (Spec.map φ)).obj A ≅ (pullback c).obj M) :
    chart φ ψ a b w c c' hc e =
      (SchemePullbackSquare.squareIso (Spec.map φ) (Spec.map ψ) (Spec.map a)
        (Spec.map b) (spec_square φ ψ a b w)).app A ≪≫ (pullback (Spec.map b)).mapIso e ≪≫
          (comparison (Spec.map b) c c' hc).app M := by
  simpa only [chart, Iso.trans_assoc] using
    congrArg (fun k ↦ k ≪≫ (comparison (Spec.map b) c c' hc).app M)
    (reconstruction_eq_scheme φ ψ a b w e)

/-- A section of an affine refinement retains the original named reconstruction. -/
@[reassoc]
lemma chart_section (c : Spec S ⟶ Y) (c' : Spec S' ⟶ Y)
    (hc : Spec.map b ≫ c = c') (s : Spec R' ⟶ Spec S')
    (hs : s ≫ Spec.map ψ = 𝟙 (Spec R')) (t : Spec R' ⟶ Spec S)
    (ht : s ≫ Spec.map b = t) (ha : t ≫ Spec.map φ = Spec.map a)
    (d : Spec R' ⟶ Y) (hd : s ≫ c' = d) (hcd : t ≫ c = d)
    {A : (Spec R).Modules} {M : Y.Modules}
    (e : (pullback (Spec.map φ)).obj A ≅ (pullback c).obj M) :
    (pullback s).map (chart φ ψ a b w c c' hc e).hom ≫
        (comparison s c' d hd).hom.app M =
      (retractIso s (Spec.map ψ) hs ((pullback (Spec.map a)).obj A)).hom ≫
        (comparison t (Spec.map φ) (Spec.map a) ha).inv.app A ≫
        (pullback t).map e.hom ≫ (comparison t c d hcd).hom.app M := by
  have hh := congrArg (fun k ↦ (pullback s).map k.hom ≫
    (comparison s c' d hd).hom.app M) (chart_eq_scheme φ ψ a b w c c' hc e)
  exact hh.trans (SchemePullbackSquare.named_reconstruction_section
    (Spec.map φ) (Spec.map ψ) (Spec.map a) (Spec.map b) (spec_square φ ψ a b w)
    s hs t ht ha c c' hc d hd hcd e)


end FLT.Mazur.AffineNamedRefinementReconstruction

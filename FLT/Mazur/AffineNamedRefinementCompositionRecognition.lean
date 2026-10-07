/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNamedRefinementNaturality

/-!
# Composition with independently named reconstruction charts

Recognize the intermediate, base composition, and final charts before
specializing the composition theorem to effectively descended sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineNamedRefinementReconstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' R'' S'' : CommRingCat.{u}} {Y : Scheme.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (χ : R'' ⟶ S'')
variable (a : R ⟶ R') (b : S ⟶ S') (c : R' ⟶ R'') (d : S' ⟶ S'')
variable (w : φ ≫ b = a ≫ ψ) (v : ψ ≫ d = c ≫ χ)
variable (t : Spec S ⟶ Y) (t' : Spec S' ⟶ Y) (t'' : Spec S'' ⟶ Y)
variable (ht : Spec.map b ≫ t = t') (ht' : Spec.map d ≫ t' = t'')
variable {A : (Spec R).Modules} {M : Y.Modules}

/-- Composition coherence transported to explicitly identified reconstruction charts. -/
theorem chart_composition_of_eq
    (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M)
    (E : (pullback (Spec.map ψ)).obj ((pullback (Spec.map a)).obj A) ≅
      (pullback t').obj M) (hE : E = chart φ ψ a b w t t' ht e)
    (B : (pullback (Spec.map c)).obj ((pullback (Spec.map a)).obj A) ≅
      (pullback (Spec.map (a ≫ c))).obj A)
    (hB : B = AffineRefinementPullback.compositionChart a c A)
    (G : (pullback (Spec.map χ)).obj ((pullback (Spec.map (a ≫ c))).obj A) ≅
      (pullback t'').obj M)
    (hG : G = chart φ χ (a ≫ c) (b ≫ d)
      (AffineRefinementPullback.composite_square φ ψ χ a b c d w v)
      t t'' (cover_comp b d t t' t'' ht ht') e) :
    (chart ψ χ c d v t' t'' ht' E).hom = (pullback (Spec.map χ)).map B.hom ≫ G.hom := by
  rw [hE, hB, hG]
  exact chart_composition φ ψ χ a b c d w v t t' t'' ht ht' e

end FLT.Mazur.AffineNamedRefinementReconstruction

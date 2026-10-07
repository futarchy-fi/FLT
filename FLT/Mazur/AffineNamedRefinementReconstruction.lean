/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRefinementComposition

/-!
# Reconstruction on named covering charts

Refine a reconstruction and identify the resulting pullback with a named
covering chart. These identifications compose by pullback associativity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineNamedRefinementReconstruction
open AffineRefinementPullback SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' R'' S'' : CommRingCat.{u}} {Y : Scheme.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (χ : R'' ⟶ S'')
variable (a : R ⟶ R') (b : S ⟶ S') (c : R' ⟶ R'') (d : S' ⟶ S'')
variable (w : φ ≫ b = a ≫ ψ) (v : ψ ≫ d = c ≫ χ)
variable (t : Spec S ⟶ Y) (t' : Spec S' ⟶ Y) (t'' : Spec S'' ⟶ Y)
variable (ht : Spec.map b ≫ t = t') (ht' : Spec.map d ≫ t' = t'')
variable {A : (Spec R).Modules} {M : Y.Modules}

/-- Refinement reconstruction with an independently named covering chart endpoint. -/
def chart (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M) :
    (pullback (Spec.map ψ)).obj ((pullback (Spec.map a)).obj A) ≅
      (pullback t').obj M :=
  reconstruction φ ψ a b w e ≪≫ (comparison (Spec.map b) t t' ht).app M

include ht ht' in
/-- The composed covering refinement still factors through its named chart. -/
theorem cover_comp : Spec.map (b ≫ d) ≫ t = t'' := by
  rw [Spec.map_comp, Category.assoc, ht, ht']

/-- Appending an isomorphism to a reconstruction commutes with affine refinement. -/
theorem reconstruction_trans {U V : (Spec S).Modules}
    (e : (pullback (Spec.map φ)).obj A ≅ U) (f : U ≅ V) :
    (reconstruction φ ψ a b w (e ≪≫ f)).hom =
      (reconstruction φ ψ a b w e).hom ≫ (pullback (Spec.map b)).map f.hom := by
  simp only [reconstruction, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]

/-- The named chart adds exactly the geometric cover path comparison. -/
theorem chart_hom (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M) :
    (chart φ ψ a b w t t' ht e).hom =
      (reconstruction φ ψ a b w e).hom ≫ (comparison (Spec.map b) t t' ht).hom.app M :=
  rfl

/-- The named reconstruction is refinement followed by cover normalization. -/
theorem chart_eq (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M) :
    chart φ ψ a b w t t' ht e =
      reconstruction φ ψ a b w e ≪≫ (comparison (Spec.map b) t t' ht).app M := rfl

private theorem scheme_composition_hom {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (k : U ⟶ W) (h : f ≫ g = k) (N : W.Modules) :
    (SchemePullbackSquare.compositionChart f g k h N).hom =
      (comparison f g k h).hom.app N := rfl

/-- Expose the morphism of a composition chart before specializing its sheaf. -/
theorem compositionChart_hom (N : (Spec S).Modules) :
    (compositionChart b d N).hom =
      (comparison (Spec.map d) (Spec.map b) (Spec.map (b ≫ d))
        (Spec.map_comp b d).symm).hom.app N :=
  scheme_composition_hom (Spec.map d) (Spec.map b) (Spec.map (b ≫ d))
    (Spec.map_comp b d).symm N

attribute [local irreducible] chart reconstruction compositionChart
attribute [local irreducible] comparison AffineRefinementPullback.squareIso

/-- Appending the final cover normalization to reconstruction composition. -/
theorem normalized_composition
    (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M) :
    (reconstruction ψ χ c d v (A := (pullback (Spec.map a)).obj A)
      (reconstruction φ ψ a b w e)).hom ≫
        (compositionChart b d ((pullback t).obj M)).hom ≫
        (comparison (Spec.map (b ≫ d)) t t'' (cover_comp b d t t' t'' ht ht')).hom.app M =
      (pullback (Spec.map χ)).map (compositionChart a c A).hom ≫
        (reconstruction φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v) e).hom ≫
        (comparison (Spec.map (b ≫ d)) t t'' (cover_comp b d t t' t'' ht ht')).hom.app M :=
  reconstruction_composition_assoc φ ψ χ a b c d w v (A := A) (M := (pullback t).obj M) e
    ((comparison (Spec.map (b ≫ d)) t t'' (cover_comp b d t t' t'' ht ht')).hom.app M)

/-- Refinement of a named chart factors through the cover path normalization. -/
theorem chart_step (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M) :
    (reconstruction ψ χ c d v (A := (pullback (Spec.map a)).obj A)
      (chart φ ψ a b w t t' ht e)).hom =
      (reconstruction ψ χ c d v (A := (pullback (Spec.map a)).obj A)
      (reconstruction φ ψ a b w e)).hom ≫
        (pullback (Spec.map d)).map ((comparison (Spec.map b) t t' ht).hom.app M) := by
  rw [chart_eq φ ψ a b w t t' ht e]
  exact reconstruction_trans ψ χ c d v (A := (pullback (Spec.map a)).obj A)
      (reconstruction φ ψ a b w e)
    ((comparison (Spec.map b) t t' ht).app M)

private theorem compose_normalizations {C : Type*} [Category C]
    {X U V W T Z : C} (K : X ⟶ Z) (F : X ⟶ V) (R : X ⟶ U)
    (g : U ⟶ V) (h : V ⟶ Z) (j : U ⟶ W) (k : W ⟶ Z)
    (m : X ⟶ T) (n : T ⟶ W) (q : T ⟶ Z)
    (h0 : K = F ≫ h) (h1 : F = R ≫ g) (h2 : g ≫ h = j ≫ k)
    (h3 : R ≫ j ≫ k = m ≫ n ≫ k) (h4 : q = n ≫ k) : K = m ≫ q := by
  rw [h0, h1, Category.assoc, h2, h3, ← h4]

/-- The two normalizations of the covering path agree. -/
theorem cover_path : (pullback (Spec.map d)).map ((comparison (Spec.map b) t t' ht).hom.app M) ≫
      (comparison (Spec.map d) t' t'' ht').hom.app M =
    (compositionChart b d ((pullback t).obj M)).hom ≫
      (comparison (Spec.map (b ≫ d)) t t''
        (cover_comp b d t t' t'' ht ht')).hom.app M := by
  have hp := comparison_assoc (Spec.map d) (Spec.map b) t (Spec.map (b ≫ d)) t' t''
    (Spec.map_comp b d).symm ht ht' (cover_comp b d t t' t'' ht ht') M
  rw [compositionChart_hom b d ((pullback t).obj M)]
  exact hp

/-- Reconstructing through two named charts agrees with their composite refinement. -/
theorem chart_composition (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M) :
    (chart ψ χ c d v t' t'' ht' (A := (pullback (Spec.map a)).obj A)
      (M := M) (chart φ ψ a b w t t' ht e)).hom =
      (pullback (Spec.map χ)).map (compositionChart a c A).hom ≫
        (chart φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v)
          t t'' (cover_comp b d t t' t'' ht ht') e).hom := by
  exact compose_normalizations _ _ _ _ _ _ _ _ _ _
    (chart_hom ψ χ c d v t' t'' ht' (A := (pullback (Spec.map a)).obj A)
      (M := M) (chart φ ψ a b w t t' ht e))
    (chart_step φ ψ χ a b c d w v t t' ht e)
    (cover_path b d t t' t'' ht ht' (M := M))
    (normalized_composition φ ψ χ a b c d w v t t' t'' ht ht' e)
    (chart_hom φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v)
      t t'' (cover_comp b d t t' t'' ht ht') e)

end FLT.Mazur.AffineNamedRefinementReconstruction

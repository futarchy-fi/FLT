/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCoefficientBaseChangeEtale

/-!
# Relative source comparisons for Cartesian translation changes

A Cartesian translation square remains Cartesian after retaining the new
ground coordinate. Etale translations over their own ground bases therefore
supply an etale relative source map for every ground change.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeCoefficientBaseChange
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme} (a : S' ⟶ S) {A V : Over S} {B W : Over S'}
  (u : (Over.map a).obj B ⟶ A) (b : B ⟶ W) (v : A ⟶ V)
  (t : (Over.map a).obj W ⟶ V)
  (H : IsPullback u.left b.left v.left t.left)

include H in
/-- Both coefficients of the relative source square agree as scheme morphisms. -/
theorem relativeSource_square :
    (projection a u (𝟙 A)).left ≫ (baseMap a v).left =
      b.left ≫ (projection a t (𝟙 V)).left := by
  rw [← Over.comp_left, ← projection_factor]
  apply pullback.hom_ext
  · simpa only [projection, Over.homMk_left, Over.id_left, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id] using H.w
  · simpa only [projection, Over.homMk_left, Category.assoc, pullback.lift_snd] using b.w.symm

include H in
/-- The full source is pulled back from the changed original source, not a selected fiber. -/
theorem relativeSource_isPullback :
    IsPullback (projection a u (𝟙 A)).left b.left
      (baseMap a v).left (projection a t (𝟙 V)).left := by
  have H' : IsPullback
      ((projection a u (𝟙 A)).left ≫ (toOld a (T := A)).left) b.left v.left
      ((projection a t (𝟙 V)).left ≫ (toOld a (T := V)).left) := by
    have hu := congrArg Over.Hom.left (projection_toOld a u (𝟙 A))
    have ht := congrArg Over.Hom.left (projection_toOld a t (𝟙 V))
    change (projection a u (𝟙 A)).left ≫ (toOld a).left = u.left ≫ 𝟙 A.left at hu
    change (projection a t (𝟙 V)).left ≫ (toOld a).left = t.left ≫ 𝟙 V.left at ht
    simp only [Category.comp_id] at hu ht
    rw [hu, ht]
    exact H
  exact H'.of_right (relativeSource_square a u b v t H) (baseMap_isPullback a v)

/-- Maps between etale translations over the new ground base are etale. -/
theorem relativeTranslation_etale [Etale V.hom] [Etale W.hom] :
    Etale (projection a t (𝟙 V)).left := by
  let _ : Etale (target a (T := V)).hom :=
    inferInstanceAs (Etale (pullback.snd V.hom a))
  let _ : Etale ((projection a t (𝟙 V)).left ≫ (target a (T := V)).hom) := by
    rw [(projection a t (𝟙 V)).w]
    infer_instance
  exact Etale.of_comp (projection a t (𝟙 V)).left (target a (T := V)).hom

include H in
/-- No etaleness, flatness, or monicity assumption is required on the ground change. -/
theorem relativeSource_etale [Etale V.hom] [Etale W.hom] :
    Etale (projection a u (𝟙 A)).left := by
  let _ := relativeTranslation_etale a t
  exact MorphismProperty.of_isPullback (relativeSource_isPullback a u b v t H).flip
    (inferInstanceAs (Etale (projection a t (𝟙 V)).left))

end FLT.Mazur.RelativeCoefficientBaseChange

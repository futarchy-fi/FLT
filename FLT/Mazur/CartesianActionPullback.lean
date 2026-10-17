/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGraphTransport

/-!
# Whole actions on specified Cartesian squares

The actual Cartesian group and curve comparisons identify an action whenever
its composite with the original curve projection agrees with the original action.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
namespace FLT.Mazur.CartesianActionPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (f : T ⟶ S) {G X : Over S} {H Y : Over T}

/-- The relative isomorphism supplied by an actual Cartesian square. -/
def comparison (p : Y.left ⟶ X.left) (hs : IsPullback p Y.hom X.hom f) :
    Y ≅ (Over.pullback f).obj X :=
  Over.isoMk hs.isoPullback hs.isoPullback_hom_snd

/-- The comparison retains the specified original curve projection. -/
@[reassoc] theorem comparison_fst (p : Y.left ⟶ X.left)
    (hs : IsPullback p Y.hom X.hom f) :
    (comparison f p hs).hom.left ≫ pullback.fst X.hom f = p :=
  hs.isoPullback_hom_fst

/-- The underlying input of a pulled-back whole action. -/
def input : ((Over.pullback f).obj G ⊗ (Over.pullback f).obj X).left ⟶ (G ⊗ X).left :=
  (Functor.LaxMonoidal.μ (Over.pullback f) G X).left ≫ pullback.fst (G ⊗ X).hom f

/-- The pulled-back action retains the original action after the curve projection. -/
@[reassoc] theorem action_fst (a : G ⊗ X ⟶ X) :
    (Functor.LaxMonoidal.μ (Over.pullback f) G X ≫ (Over.pullback f).map a).left ≫
      pullback.fst X.hom f = input f ≫ a.left := by
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
  rfl

/-- The first input remains the actual pulled-back group projection. -/
@[reassoc] theorem input_fst : input f (G := G) (X := X) ≫ (fst G X).left =
    (fst ((Over.pullback f).obj G) ((Over.pullback f).obj X)).left ≫
      pullback.fst G.hom f := Over.μ_pullback_left_fst_fst G X

/-- The second input remains the actual pulled-back curve projection. -/
@[reassoc] theorem input_snd : input f (G := G) (X := X) ≫ (snd G X).left =
    (snd ((Over.pullback f).obj G) ((Over.pullback f).obj X)).left ≫
      pullback.fst X.hom f := Over.μ_pullback_left_fst_snd G X

/-- Cartesian comparisons identify the entire action, including singular inputs. -/
theorem action_comparison (g : H.left ⟶ G.left) (p : Y.left ⟶ X.left)
    (hg : IsPullback g H.hom G.hom f) (hp : IsPullback p Y.hom X.hom f)
    (i : (H ⊗ Y).left ⟶ (G ⊗ X).left)
    (hi₁ : i ≫ (fst G X).left = (fst H Y).left ≫ g)
    (hi₂ : i ≫ (snd G X).left = (snd H Y).left ≫ p)
    (a : G ⊗ X ⟶ X) (b : H ⊗ Y ⟶ Y) (hab : b.left ≫ p = i ≫ a.left) :
    b ≫ (comparison f p hp).hom =
      ((comparison f g hg).hom ⊗ₘ (comparison f p hp).hom) ≫
        Functor.LaxMonoidal.μ (Over.pullback f) G X ≫ (Over.pullback f).map a := by
  have hi : ((comparison f g hg).hom ⊗ₘ (comparison f p hp).hom).left ≫ input f = i := by
    apply pullback.hom_ext
    · change _ ≫ (fst G X).left = _
      rw [Category.assoc, input_fst, ← Category.assoc, ← Over.comp_left, tensorHom_fst]
      simpa only [Over.comp_left, Category.assoc, comparison_fst,
        Over.fst_left, Over.snd_left] using hi₁.symm
    · change _ ≫ (snd G X).left = _
      rw [Category.assoc, input_snd, ← Category.assoc, ← Over.comp_left, tensorHom_snd]
      simpa only [Over.comp_left, Category.assoc, comparison_fst,
        Over.fst_left, Over.snd_left] using hi₂.symm
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, comparison_fst]
    have ha := action_fst f a
    simp only [Over.comp_left, Category.assoc] at ha
    rw [ha]
    rw [← Category.assoc, hi, hab]
  · exact (b ≫ (comparison f p hp).hom).w.trans
      (((comparison f g hg).hom ⊗ₘ (comparison f p hp).hom) ≫
        Functor.LaxMonoidal.μ (Over.pullback f) G X ≫ (Over.pullback f).map a).w.symm

end FLT.Mazur.CartesianActionPullback

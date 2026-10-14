/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealStalkDescent

/-!
# Regularity of an actual pulled Cartier parameter

If the full pulled ideal is Cartier, the original parameter remains regular
in source sections. The morphism need not be flat and the source need not be
affine: Cartier stalk generators and sheaf separation detect cancellation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) (I : Y.IdealSheafData)
  (a : Γ(Y, ⊤)) (ha : I.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {a})
  (hI : EffectiveCartier (I.comap f))

include ha hI

/-- Every actual pulled parameter germ is regular because it generates a Cartier ideal. -/
theorem cartierPullbackParameter_germ_regular (x : X) :
    IsRegular (X.presheaf.Γgerm x (f.appTop a)) := by
  obtain ⟨b, hb, hIb⟩ := hI.stalk_generator x
  have he : stalkIdeal (I.comap f) x =
      Ideal.span {X.presheaf.Γgerm x (f.appTop a)} := by
    rw [stalkIdeal_comap, stalkIdeal_eq_map I (f x) ⟨⊤, isAffineOpen_top Y⟩ trivial,
      ha, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 2
    simp [TopCat.Presheaf.Γgerm, Scheme.Hom.appTop]
  apply isRegular_of_mem_span_singleton hb
  rw [← he, hIb]
  exact Ideal.mem_span_singleton_self b

/-- The actual pulled parameter is regular in global sections even for a nonaffine source. -/
theorem cartierPullbackParameter_regular : IsRegular (f.appTop a) := by
  have hl : IsLeftRegular (f.appTop a) := by
    intro b c he
    apply TopCat.Presheaf.section_ext X.sheaf ⊤ b c
    intro x hx
    change X.presheaf.germ ⊤ x hx b = X.presheaf.germ ⊤ x hx c
    apply (cartierPullbackParameter_germ_regular f I a ha hI x).left
    simpa only [map_mul, TopCat.Presheaf.Γgerm] using congrArg (X.presheaf.germ ⊤ x hx) he
  exact ⟨hl, fun b c he => hl (by simpa only [mul_comm] using he)⟩

end FLT.Mazur.FCurve

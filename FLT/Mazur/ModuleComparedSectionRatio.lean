/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioCoordinates

/-!
# Ratios through a component comparison with an identified denominator

Prove the transport before substituting concrete schemes and divisor sheaves.
The denominator equality is supplied by the actual sheaf comparison.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
/-- Equal scheme maps induce equal ratios without unfolding their pullback functors. -/
lemma sectionRatio_pullGlobal_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g)
    (M : Y.Modules) (s t : Γ(M, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal f M s))]
    [IsIso (globalSectionHom _ (pullGlobal g M s))] :
    sectionRatio _ (pullGlobal f M s) (pullGlobal f M t) =
      sectionRatio _ (pullGlobal g M s) (pullGlobal g M t) := by
  subst g
  rfl

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (M : Z.Modules) (N : Y.Modules) (e : (pullback g).obj M ≅ N)
  (s : Γ(M, ⊤)) (s' : Γ(N, ⊤)) (he : e.hom.app ⊤ (pullGlobal g M s) = s')
  [IsIso (globalSectionHom _ (pullGlobal f N s'))]

include he in
/-- An identified denominator generates on the actual composite pullback. -/
lemma comparedSection_isIso :
    IsIso (globalSectionHom _ (pullGlobal (f ≫ g) M s)) := by
  have : IsIso (globalSectionHom _ (pullGlobal f N
      (e.hom.app ⊤ (pullGlobal g M s)))) := by rw [he]; infer_instance
  have := globalSectionHom_isIso_pullback_transport f e (pullGlobal g M s)
  exact globalSectionHom_isIso_comp_pullGlobal f g M s

/-- Ratios commute with a component comparison identifying the denominator. -/
lemma comparedSection_ratio (t : Γ(M, ⊤)) :
    let := comparedSection_isIso f g M N e s s' he
    sectionRatio _ (pullGlobal (f ≫ g) M s) (pullGlobal (f ≫ g) M t) =
      sectionRatio _ (pullGlobal f N s')
        (pullGlobal f N (e.hom.app ⊤ (pullGlobal g M t))) := by
  have : IsIso (globalSectionHom _ (pullGlobal f N
      (e.hom.app ⊤ (pullGlobal g M s)))) := by rw [he]; infer_instance
  have := globalSectionHom_isIso_pullback_transport f e (pullGlobal g M s)
  refine (sectionRatio_comp_pullGlobal f g M s t).trans
    ((sectionRatio_pullGlobal_transport f e (pullGlobal g M s) (pullGlobal g M t)).trans ?_)
  apply (sectionRatio_eq_iff _ _ _ _).mpr
  rw [he]
  exact sectionRatio_smul _ _ _

end FLT.Mazur.FCurve

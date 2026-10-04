/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleComparedSectionRatio

/-!
# Sealed ratios of pulled-back sections

Keep the pullback adjunction and inverse section morphism behind a kernel
boundary. Equal maps and component comparisons act on this ratio through
identities proved for arbitrary schemes, before concrete specialization.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y Z : Scheme.{u}}

/-- The actual pulled-back ratio, sealed against unfolding of the adjunction. -/
irreducible_def pullbackSectionRatio (f : X ⟶ Y) (M : Y.Modules) (s t : Γ(M, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal f M s))] : Γ(X, ⊤) :=
  sectionRatio _ (pullGlobal f M s) (pullGlobal f M t)

/-- Equal scheme maps give equal sealed ratios. -/
lemma pullbackSectionRatio_congr {f g : X ⟶ Y} (hfg : f = g)
    (M : Y.Modules) (s t : Γ(M, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal f M s))]
    [IsIso (globalSectionHom _ (pullGlobal g M s))] :
    pullbackSectionRatio f M s t = pullbackSectionRatio g M s t := by
  subst g
  rfl

/-- A component comparison transports sealed ratios at the level of sections. -/
lemma pullbackSectionRatio_compared (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : Y.Modules) (e : (pullback g).obj M ≅ N)
    (s : Γ(M, ⊤)) (s' : Γ(N, ⊤)) (he : e.hom.app ⊤ (pullGlobal g M s) = s')
    [IsIso (globalSectionHom _ (pullGlobal f N s'))] (t : Γ(M, ⊤)) :
    let := comparedSection_isIso f g M N e s s' he
    pullbackSectionRatio (f ≫ g) M s t =
      pullbackSectionRatio f N s' (e.hom.app ⊤ (pullGlobal g M t)) := by
  dsimp only
  rw [pullbackSectionRatio_def, pullbackSectionRatio_def]
  exact comparedSection_ratio f g M N e s s' he t

/-- Explicit numerator identification avoids conversion inside a concrete ratio. -/
lemma pullbackSectionRatio_compared_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : Y.Modules) (e : (pullback g).obj M ≅ N)
    (s : Γ(M, ⊤)) (s' : Γ(N, ⊤)) (he : e.hom.app ⊤ (pullGlobal g M s) = s')
    [IsIso (globalSectionHom _ (pullGlobal f N s'))]
    (t : Γ(M, ⊤)) (t' : Γ(N, ⊤)) (ht : e.hom.app ⊤ (pullGlobal g M t) = t') :
    let := comparedSection_isIso f g M N e s s' he
    pullbackSectionRatio (f ≫ g) M s t = pullbackSectionRatio f N s' t' := by
  subst t'
  exact pullbackSectionRatio_compared f g M N e s s' he t

/-- Both map and section identifications are resolved before concrete specialization. -/
lemma pullbackSectionRatio_compared_of_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (hk : k = f ≫ g)
    (M : Z.Modules) (N : Y.Modules) (e : (pullback g).obj M ≅ N)
    (s : Γ(M, ⊤)) (s' : Γ(N, ⊤)) (he : e.hom.app ⊤ (pullGlobal g M s) = s')
    [IsIso (globalSectionHom _ (pullGlobal f N s'))]
    [IsIso (globalSectionHom _ (pullGlobal k M s))]
    (t : Γ(M, ⊤)) (t' : Γ(N, ⊤)) (ht : e.hom.app ⊤ (pullGlobal g M t) = t') :
    pullbackSectionRatio k M s t = pullbackSectionRatio f N s' t' := by
  have := comparedSection_isIso f g M N e s s' he
  exact (pullbackSectionRatio_congr hk M s t).trans
    (pullbackSectionRatio_compared_eq f g M N e s s' he t t' ht)

end FLT.Mazur.FCurve

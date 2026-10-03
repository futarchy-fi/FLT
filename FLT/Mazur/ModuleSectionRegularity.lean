/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Regular scalar cancellation on trivial module sheaves

A trivialization on the whole open gives a global trivialization. Regular
functions then act injectively on sections. Local coordinate relations and
pullback transports allow comparisons of independently chosen chart sections.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y Z : Scheme.{u}}
/-- A trivialization over the whole open gives an isomorphism on the original scheme. -/
def moduleTopTrivialization (M : X.Modules)
    (e : M.restrict (⊤ : X.Opens).ι ≅ structureModule (⊤ : X.Opens).toScheme) :
    M ≅ structureModule X :=
  (restrictFunctorId.app M).symm ≪≫
    (restrictFunctorCongr X.topIso.inv_hom_id.symm).app M ≪≫
    (restrictFunctorComp X.topIso.inv (⊤ : X.Opens).ι).app M ≪≫
    (restrictFunctor X.topIso.inv).mapIso e ≪≫ restrictUnitIso X.topIso.inv
/-- Regular global functions act injectively on a trivial module sheaf. -/
lemma regular_smul_of_trivialization (M : X.Modules) (e : M ≅ structureModule X)
    (r : Γ(X, ⊤)) (hr : IsRegular r) : IsSMulRegular Γ(M, ⊤) r := by
  intro s t h
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  apply hr.left
  simpa only [Hom.app_smul, smul_eq_mul] using congrArg (e.hom.app ⊤) h
/-- Compare a pulled-back global section with any independent local section. -/
lemma pullGlobal_local_relation (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (e : Γ((pullback g).obj M, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(Y, ⊤))
    (c : Γ(M, ⊤)) (s : Γ((pullback g).obj M, ⊤)) :
    f.appTop (e (pullGlobal g M c)) •
      ((pullbackComp f g).hom.app M).app ⊤ (pullGlobal f _ s) =
    f.appTop (e s) • pullGlobal (f ≫ g) M c := by
  have h : e (pullGlobal g M c) • s = e s • pullGlobal g M c := by
    apply e.injective
    rw [e.map_smul, e.map_smul]
    exact mul_comm _ _
  have h' := congrArg (fun t ↦ ((pullbackComp f g).hom.app M).app ⊤
    (pullGlobal f ((pullback g).obj M) t)) h
  simpa only [map_smulₛₗ, Hom.app_smul, pullGlobal_comp_hom] using h'
/-- Section pullback respects the canonical comparison for equal scheme morphisms. -/
lemma pullGlobal_congr {f g : X ⟶ Y} (h : f = g) (M : Y.Modules)
    (s : Γ(M, ⊤)) :
    ((pullbackCongr h).hom.app M).app ⊤ (pullGlobal f M s) = pullGlobal g M s := by
  subst g
  rfl
/-- Transport a local coordinate relation to an equal composite scheme map. -/
lemma pullGlobal_local_relation_congr {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k) (M : Z.Modules)
    (e : Γ((pullback g).obj M, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(Y, ⊤))
    (c : Γ(M, ⊤)) (s : Γ((pullback g).obj M, ⊤)) :
    f.appTop (e (pullGlobal g M c)) •
      ((pullbackCongr h).hom.app M).app ⊤
        (((pullbackComp f g).hom.app M).app ⊤ (pullGlobal f _ s)) =
    f.appTop (e s) • pullGlobal k M c := by
  subst k
  exact pullGlobal_local_relation f g M e c s
/-- Pull a chart section to the module along the composite scheme morphism. -/
def pullOverlap {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ((pullback g).obj M, ⊤)) :
    Γ((pullback (f ≫ g)).obj M, ⊤) :=
  ((pullbackComp f g).hom.app M).app ⊤ (pullGlobal f _ s)
/-- Pull a chart section to an equal, specified composite scheme morphism. -/
def pullOverlapAlong {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k) (M : Z.Modules)
    (s : Γ((pullback g).obj M, ⊤)) : Γ((pullback k).obj M, ⊤) :=
  ((pullbackCongr h).hom.app M).app ⊤ (pullOverlap f g M s)
/-- Compatible coordinates give equality of independently pulled-back local sections. -/
lemma pullGlobal_local_glue {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (j : Y ⟶ Z) (g : X ⟶ W) (k : W ⟶ Z)
    (h : f ≫ j = g ≫ k) (M : Z.Modules)
    (e : Γ((pullback j).obj M, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(Y, ⊤))
    (e' : Γ((pullback k).obj M, ⊤) ≃ₗ[Γ(W, ⊤)] Γ(W, ⊤))
    (c : Γ(M, ⊤)) (s : Γ((pullback j).obj M, ⊤))
    (t : Γ((pullback k).obj M, ⊤)) (v : Γ(X, ⊤))
    (hc : IsSMulRegular Γ((pullback (f ≫ j)).obj M, ⊤)
      (g.appTop (e' (pullGlobal k M c))))
    (hv : g.appTop (e' (pullGlobal k M c)) = v * f.appTop (e (pullGlobal j M c)))
    (hst : g.appTop (e' t) = v * f.appTop (e s)) :
    pullOverlap f j M s = pullOverlapAlong g k (f ≫ j) h.symm M t := by
  unfold pullOverlapAlong pullOverlap
  apply hc
  dsimp only
  rw [pullGlobal_local_relation_congr g k (f ≫ j) h.symm M e' c t]
  rw [hv, mul_smul, pullGlobal_local_relation f j M e c s, hst, mul_smul]
end FLT.Mazur.FCurve

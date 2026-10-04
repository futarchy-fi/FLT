/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SealedLineRestriction
public import FLT.Mazur.ModuleDisjointSectionGluing
/-!
# Sealed restrictions on global sections

Composition identifies restriction with ordinary pullback followed by a section
isomorphism. Open covers detect equality; disjoint covers allow arbitrary values.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LinePullbackRestriction
open FCurve
variable {X Y Z : Scheme.{u}}
/-- Compose the two pullbacks and transport through the commuting triangle. -/
def sectionTargetIso (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (w : s ≫ p = q)
    (L : Z.Modules) : (pullback s).obj ((pullback p).obj L) ≅ (pullback q).obj L :=
  LineEndpointTransport.iso p s q w (Iso.refl _)
/-- The sealed map evaluates as pullback followed by the target isomorphism. -/
lemma sealedAlong_apply (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (w : s ≫ p = q)
    (L : Z.Modules) (t : Γ((pullback p).obj L, ⊤)) :
    (sealedAlong s p q w L).app ⊤ t =
      (sectionTargetIso s p q w L).hom.app ⊤ (pullGlobal s ((pullback p).obj L) t) := by
  simpa only [sectionTargetIso, Iso.refl_hom, Hom.id_app, AddCommGrpCat.id_apply] using
    sealedAlong_eq_transport p s q w (Iso.refl _) t
/-- Restrictions through an open cover jointly detect equality of global sections. -/
lemma sealedAlong_cover_injective (C : Y.OpenCover) (p : Y ⟶ Z)
    (q : ∀ i, C.X i ⟶ Z) (w : ∀ i, C.f i ≫ p = q i) (L : Z.Modules) :
    Function.Injective (fun t : Γ((pullback p).obj L, ⊤) ↦
      fun i ↦ (sealedAlong (C.f i) p (q i) (w i) L).app ⊤ t) := by
  intro s t h
  apply pullGlobal_openCover_ext C ((pullback p).obj L) s t
  intro i
  apply (ConcreteCategory.bijective_of_isIso
    ((sectionTargetIso (C.f i) p (q i) (w i) L).hom.app ⊤)).injective
  simpa only [← sealedAlong_apply] using congrFun h i
/-- Disjoint-cover restrictions allow arbitrary component sections. -/
lemma sealedAlong_disjointCover_bijective (C : Y.OpenCover)
    (hd : Pairwise (fun i j ↦ Disjoint (C.f i ''ᵁ ⊤) (C.f j ''ᵁ ⊤)))
    (p : Y ⟶ Z) (q : ∀ i, C.X i ⟶ Z) (w : ∀ i, C.f i ≫ p = q i) (L : Z.Modules) :
    Function.Bijective (fun t : Γ((pullback p).obj L, ⊤) ↦
      fun i ↦ (sealedAlong (C.f i) p (q i) (w i) L).app ⊤ t) := by
  refine ⟨sealedAlong_cover_injective C p q w L, ?_⟩
  intro s
  let v i := (sectionTargetIso (C.f i) p (q i) (w i) L).inv.app ⊤ (s i)
  obtain ⟨t, ht⟩ := (pullGlobal_disjointCover_bijective C hd ((pullback p).obj L)).surjective v
  refine ⟨t, funext fun i ↦ ?_⟩
  exact (sealedAlong_apply (C.f i) p (q i) (w i) L t).trans
    ((congrArg ((sectionTargetIso (C.f i) p (q i) (w i) L).hom.app ⊤) (congrFun ht i)).trans
      (sectionIso_hom_inv (sectionTargetIso (C.f i) p (q i) (w i) L) ⊤ (s i)))
end FLT.Mazur.LinePullbackRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Descent along two open charts

A cartesian square of open immersions whose bottom maps cover the target
is also a pushout. This permits gluing with an explicit intersection chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.BinaryOpenDescent

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V)
  (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
  (h : IsPullback a b i j)
  (hc : ∀ x : X, x ∈ Set.range i ∨ x ∈ Set.range j)

/-- The binary cover associated to two jointly surjective open immersions. -/
def cover : X.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Bool
    (fun k ↦ if k then V else U)
    (fun k ↦ Bool.rec i j k)
    (by
      intro x
      rcases hc x with hx | hx
      · exact ⟨false, hx⟩
      · exact ⟨true, hx⟩)
    (by intro k; cases k <;> infer_instance)

variable {Y : Scheme.{u}} (f : U ⟶ Y) (g : V ⟶ Y) (w : a ≫ f = b ≫ g)

include h w in
/-- Compatibility on the pullbacks in the binary cover. -/
theorem compatible :
    ∀ k l, pullback.fst ((cover i j hc).f k) ((cover i j hc).f l) ≫
      (show (cover i j hc).X k ⟶ Y from Bool.rec f g k) =
    pullback.snd _ _ ≫
      (show (cover i j hc).X l ⟶ Y from Bool.rec f g l) := by
  intro k l
  cases k <;> cases l
  · have e : pullback.fst i i = pullback.snd i i := (cancel_mono i).mp pullback.condition
    exact congrArg (fun t ↦ t ≫ f) e
  · change pullback.fst i j ≫ f = pullback.snd i j ≫ g
    rw [← cancel_epi h.isoPullback.hom]
    simpa using w
  · change pullback.fst j i ≫ g = pullback.snd j i ≫ f
    rw [← cancel_epi h.flip.isoPullback.hom]
    simpa using w.symm
  · have e : pullback.fst j j = pullback.snd j j := (cancel_mono j).mp pullback.condition
    exact congrArg (fun t ↦ t ≫ g) e

/-- Glue morphisms agreeing on the supplied cartesian intersection. -/
def desc : X ⟶ Y :=
  (cover i j hc).glueMorphisms
    (fun k ↦ Bool.rec f g k) (compatible a b i j h hc f g w)

@[reassoc (attr := simp)]
theorem inl_desc : i ≫ desc a b i j h hc f g w = f :=
  (cover i j hc).ι_glueMorphisms _ _ false

@[reassoc (attr := simp)]
theorem inr_desc : j ≫ desc a b i j h hc f g w = g :=
  (cover i j hc).ι_glueMorphisms _ _ true

include hc in
/-- Equality can be checked on the two open charts. -/
theorem hom_ext (d e : X ⟶ Y) (hi : i ≫ d = i ≫ e) (hj : j ≫ d = j ≫ e) : d = e :=
  (cover i j hc).hom_ext d e (by
    intro k
    cases k
    · exact hi
    · exact hj)

include h hc in
/-- The cartesian open cover has the arbitrary-target pushout property. -/
theorem isPushout : IsPushout a b i j := by
  refine ⟨h.toCommSq, ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ desc a b i j h hc s.inl s.inr s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    exact inl_desc a b i j h hc s.inl s.inr s.condition
  · intro s
    exact inr_desc a b i j h hc s.inl s.inr s.condition
  · intro s m hm hn
    exact hom_ext i j hc m _ (hm.trans (inl_desc ..).symm)
      (hn.trans (inr_desc ..).symm)

end FLT.Mazur.BinaryOpenDescent

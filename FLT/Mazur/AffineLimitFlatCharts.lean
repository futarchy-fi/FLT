/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredFlatChartRelations
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Common coefficient stages for flatness tests on independent affine charts

The original flat chart morphisms share a limiting base. Their ordinary
function rings form distinct filtered systems. Finite witness descent
produces one refinement for all specified chart relations simultaneously.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped BigOperators
namespace FLT.Mazur.Approximation
open RingFlatRelation
universe u
set_option backward.isDefEq.respectTransparency false
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {T : Type*} [Finite T] (X : T → I ⥤ Scheme.{u}) (S : I ⥤ Scheme.{u})
  (c : ∀ t, Cone (X t)) (d : Cone S)
  (hc : ∀ t, IsLimit (c t)) (hd : IsLimit d)
  [∀ t i, IsAffine ((X t).obj i)] [∀ i, IsAffine (S.obj i)]
  [∀ t, IsAffine (c t).pt] [IsAffine d.pt]
  (p : ∀ t, X t ⟶ S) (q : ∀ t, (c t).pt ⟶ d.pt)
  (hq : ∀ t i, (c t).π.app i ≫ (p t).app i = q t ≫ d.π.app i)

include hc hd hq in
/-- Tests on independent original affine charts descend over a single base refinement. -/
theorem exists_affine_limit_flat_chart_relations [∀ t, Flat (q t)]
    (K : T → Type*) [∀ t, Fintype (K t)]
    (i : I) (f : ∀ t, K t → Γ(S.obj i, ⊤)) (x : ∀ t, K t → Γ((X t).obj i, ⊤))
    (h : ∀ t, let f' : K t → Γ(d.pt, ⊤) := fun l ↦ (d.π.app i).appTop (f t l)
      let x' : K t → Γ((c t).pt, ⊤) := fun l ↦ ((c t).π.app i).appTop (x t l)
      ∑ l, (q t).appTop (f' l) * x' l = 0) :
    ∃ (j : I) (g : j ⟶ i), ∀ t,
      Trivial ((p t).app j).appTop.hom
        (fun l ↦ (S.map g).appTop (f t l)) (fun l ↦ ((X t).map g).appTop (x t l)) := by
  let _ (t : T) (j : Iᵒᵖ) : IsAffine ((X t).op.obj j).unop :=
    inferInstanceAs (IsAffine ((X t).obj j.unop))
  let _ (j : Iᵒᵖ) : IsAffine (S.op.obj j).unop :=
    inferInstanceAs (IsAffine (S.obj j.unop))
  let F := S.op ⋙ Scheme.Γ
  let G (t : T) := (X t).op ⋙ Scheme.Γ
  let dc := Scheme.Γ.mapCocone d.op
  let cc (t : T) := Scheme.Γ.mapCocone (c t).op
  have hdc : IsColimit dc := isColimitOfPreserves Scheme.Γ hd.op
  have hcc (t : T) : IsColimit (cc t) := isColimitOfPreserves Scheme.Γ (hc t).op
  let η (t : T) : F ⟶ G t := Functor.whiskerRight (NatTrans.op (p t)) Scheme.Γ
  have he (t : T) (j : Iᵒᵖ) : ((cc t).ι.app j).hom.comp ((η t).app j).hom =
      (q t).appTop.hom.comp (dc.ι.app j).hom := by
    exact congrArg (fun r ↦ r.appTop.hom) (hq t j.unop)
  obtain ⟨j, g, hj⟩ := exists_flat_chart_relations_stage F G dc cc hdc hcc
    η (fun t ↦ (q t).appTop.hom) he (fun t ↦ (q t).flat_appTop) K (.op i) f x h
  exact ⟨j.unop, g.unop, hj⟩

end FLT.Mazur.Approximation

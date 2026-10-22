/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredFlatRelationFamily
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Finite flatness tests on actual affine inverse systems

Apply finite witness descent to the ordinary rings of global functions on
the base and the whole affine model. Flatness is required only on the
original limiting morphism; all stage maps remain the original maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped BigOperators
namespace FLT.Mazur.Approximation
open RingFlatRelation
universe u
set_option backward.isDefEq.respectTransparency false
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (X S : I ⥤ Scheme.{u}) (c : Cone X) (d : Cone S)
  (hc : IsLimit c) (hd : IsLimit d)
  [∀ i, IsAffine (X.obj i)] [∀ i, IsAffine (S.obj i)]
  [IsAffine c.pt] [IsAffine d.pt]
  (p : X ⟶ S) (q : c.pt ⟶ d.pt)
  (hq : ∀ i, c.π.app i ≫ p.app i = q ≫ d.π.app i)

include hc hd hq in
/-- Finitely many relations on an affine model trivialize after one actual refinement. -/
theorem exists_affine_limit_flat_relation_family [Flat q]
    {T : Type*} [Finite T] (K : T → Type*) [∀ t, Fintype (K t)]
    (i : I) (f : ∀ t, K t → Γ(S.obj i, ⊤)) (x : ∀ t, K t → Γ(X.obj i, ⊤))
    (h : ∀ t, let f' : K t → Γ(d.pt, ⊤) := fun l ↦ (d.π.app i).appTop (f t l)
      let x' : K t → Γ(c.pt, ⊤) := fun l ↦ (c.π.app i).appTop (x t l)
      ∑ l, q.appTop (f' l) * x' l = 0) :
    ∃ (j : I) (g : j ⟶ i), ∀ t,
      Trivial (p.app j).appTop.hom
        (fun l ↦ (S.map g).appTop (f t l)) (fun l ↦ (X.map g).appTop (x t l)) := by
  let _ (j : Iᵒᵖ) : IsAffine (X.op.obj j).unop :=
    inferInstanceAs (IsAffine (X.obj j.unop))
  let _ (j : Iᵒᵖ) : IsAffine (S.op.obj j).unop :=
    inferInstanceAs (IsAffine (S.obj j.unop))
  let F := S.op ⋙ Scheme.Γ
  let G := X.op ⋙ Scheme.Γ
  let dc := Scheme.Γ.mapCocone d.op
  let cc := Scheme.Γ.mapCocone c.op
  have hdc : IsColimit dc := isColimitOfPreserves Scheme.Γ hd.op
  have hcc : IsColimit cc := isColimitOfPreserves Scheme.Γ hc.op
  let η : F ⟶ G := Functor.whiskerRight (NatTrans.op p) Scheme.Γ
  have he (j : Iᵒᵖ) : (cc.ι.app j).hom.comp (η.app j).hom =
      q.appTop.hom.comp (dc.ι.app j).hom := by
    exact congrArg (fun r ↦ r.appTop.hom) (hq j.unop)
  obtain ⟨j, g, hj⟩ := exists_flat_relation_family_stage F G dc cc hdc hcc
    η q.appTop.hom he q.flat_appTop K (.op i) f x h
  exact ⟨j.unop, g.unop, hj⟩

end FLT.Mazur.Approximation

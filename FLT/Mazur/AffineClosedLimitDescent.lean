/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredRingSurjectiveDescent
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventual closed immersions into a fixed affine target

In an inverse system of affine schemes with closed immersion transitions,
a finite-type structural map that is a closed immersion on the limit is
already a closed immersion after one refinement of any specified stage.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ i, IsAffine (D.obj i)]
  [∀ {i j} (g : i ⟶ j), IsClosedImmersion (D.map g)]
  {Y : Scheme.{u}} [IsAffine Y] (t : D ⟶ (Functor.const I).obj Y)
  (q : c.pt ⟶ Y) (hq : ∀ i, c.π.app i ≫ t.app i = q)

include hc hq in
/-- A closed limit map into a fixed affine scheme becomes closed at a finite stage. -/
theorem exists_isClosedImmersion_of_affine_limit [IsClosedImmersion q]
    (i : I) [LocallyOfFiniteType (t.app i)] :
    ∃ (j : I) (_ : j ⟶ i), IsClosedImmersion (t.app j) := by
  let _ (j : Iᵒᵖ) : IsAffine (D.op.obj j).unop :=
    inferInstanceAs (IsAffine (D.obj j.unop))
  let _ (j : I) : IsAffine (((Functor.const I).obj Y).obj j) :=
    inferInstanceAs (IsAffine Y)
  let F := D.op ⋙ Scheme.Γ
  let cc := Scheme.Γ.mapCocone c.op
  have hcc : IsColimit cc := isColimitOfPreserves Scheme.Γ hc.op
  have ha : (t.app i).appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  have hs : Function.Surjective ((t.app i).appTop ≫ cc.ι.app (.op i)) := by
    change Function.Surjective ((c.π.app i ≫ t.app i).appTop)
    rw [hq]
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine q).2
  have ht {j k : Iᵒᵖ} (g : j ⟶ k) : Function.Surjective (F.map g) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (D.map g.unop)).2
  obtain ⟨j, g, hg⟩ := exists_surjective_map_of_isColimit F cc hcc (.op i)
    (t.app i).appTop ha ht hs
  refine ⟨j.unop, g.unop, IsClosedImmersion.of_surjective_of_isAffine _ ?_⟩
  have he : D.map g.unop ≫ t.app i = t.app j.unop := by
    exact (t.naturality g.unop).trans (Category.comp_id _)
  change Function.Surjective ((D.map g.unop ≫ t.app i).appTop) at hg
  rwa [he] at hg

end FLT.Mazur.Approximation

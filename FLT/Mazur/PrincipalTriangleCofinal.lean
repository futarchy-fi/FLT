/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalTriangleEquations
public import FLT.Mazur.PrincipalLayeredLimits


/-!
# Cofinal finite models with commuting triangles

The finite triangular diagrams recover all three levels of principal charts.
Equations compare the complete direct and composite coordinate maps, rather
than only their images in the limiting rings.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z v' w'

variable {R : Type u} [CommRing R]
  {ι : Type v} {κ : Type w} {τ : Type v'} {E : κ → Type z} {F : τ → Type w'}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {C : τ → Type u} [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
  [∀ k, Algebra.FiniteType R (C k)]
  {src : ∀ j, E j → ι} {mid : ∀ k, F k → κ}
  {a : ∀ i, A i} {b : ∀ j, B j} {c : ∀ k, C k}
  {f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j)}
  {g : ∀ k e, Localization.Away (b (mid k e)) →ₐ[R] Localization.Away (c k)}



variable {H : τ → Type z}

variable {ds : ∀ k, H k → ι}
  {d : ∀ k e, Localization.Away (a (ds k e)) →ₐ[R] Localization.Away (c k)}



/-- Forget direct arrows and retain the layered coordinate model. -/
def principalTriangleLayeredIndex :
    PrincipalTriangleStage src mid a b c f g ds d ⥤ PrincipalLayeredStage src mid a b c f g where
  obj x := x.base
  map h := homOfLE (leOfHom h).1

variable [∀ j, Finite (E j)] [∀ k, Finite (F k)] [∀ k, Finite (H k)]

/-- Adding direct arrows preserves every layered colimit. -/
instance principalTriangleLayeredIndexFinal :
    (principalTriangleLayeredIndex (src := src) (mid := mid) (a := a) (b := b) (c := c)
      (f := f) (g := g) (ds := ds) (d := d)).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro x
    obtain ⟨y, hxy, _⟩ := exists_principalTriangleStage (ds := ds) (d := d) x
    exact ⟨y, ⟨homOfLE hxy⟩⟩
  · intro x y j k
    exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

variable (p : ∀ k e, PrincipalLayeredPath src mid (ds k e) k)

/-- Finite triangular models with actual composition equations. -/
def PrincipalTriangleEquationStage :=
  {x : PrincipalTriangleStage src mid a b c f g ds d // PrincipalTriangleEquations p x}

/-- Commuting triangles inherit their refinement order. -/
instance principalTriangleEquationStagePreorder :
    Preorder (PrincipalTriangleEquationStage (a := a) (b := b) (c := c)
      (f := f) (g := g) (d := d) p) :=
  inferInstanceAs (Preorder {x // PrincipalTriangleEquations p x})

/-- Forget the composition equations on a finite triangular model. -/
def principalTriangleEquationIndex :
    PrincipalTriangleEquationStage (a := a) (b := b) (c := c) (f := f) (g := g) (d := d) p ⥤
      PrincipalTriangleStage src mid a b c f g ds d where
  obj x := x.val
  map h := homOfLE (leOfHom h)

/-- Every two commuting triangular models have a commuting common refinement. -/
instance principalTriangleEquationStageDirected :
    IsDirectedOrder (PrincipalTriangleEquationStage (a := a) (b := b) (c := c)
      (f := f) (g := g) (d := d) p) where
  directed x y := by
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x.val y.val
    exact ⟨⟨z, principalTriangleEquations_mono p x.property hxz⟩, hxz, hyz⟩

variable (he : ∀ k e, d k e =
  principalLayeredPathMap (a := a) (b := b) (c := c) (f := f) (g := g) (p k e))

include he in
/-- Original triangle equations define a cofinal finite subsystem. -/
theorem principalTriangleEquationIndex_final :
    (principalTriangleEquationIndex (a := a) (b := b) (c := c)
      (f := f) (g := g) (d := d) p).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro x
    obtain ⟨y, hxy, _, hy⟩ := exists_principalTriangleEquations p he x
    exact ⟨⟨y, hy⟩, ⟨homOfLE hxy⟩⟩
  · intro x y j k
    exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

/-- Retain the layered model of a finite system satisfying all triangles. -/
def principalTriangleEquationLayeredIndex :
    PrincipalTriangleEquationStage (a := a) (b := b) (c := c) (f := f) (g := g) (d := d) p ⥤
      PrincipalLayeredStage src mid a b c f g :=
  principalTriangleEquationIndex p ⋙ principalTriangleLayeredIndex

include he in
/-- The simultaneous direct/composite equations preserve all layered colimits. -/
theorem principalTriangleEquationLayeredIndex_final :
    (principalTriangleEquationLayeredIndex (a := a) (b := b) (c := c)
      (f := f) (g := g) (d := d) p).Final := by
  let _ := principalTriangleEquationIndex_final p he
  exact Functor.final_comp _ _

/-- Recover any layered colimit over the subsystem with commuting triangles. -/
def principalTriangleEquationIsColimit {D : Type*} [Category D]
    {G : PrincipalLayeredStage src mid a b c f g ⥤ D} (t : Cocone G) (ht : IsColimit t) :
    IsColimit (t.whisker (principalTriangleEquationLayeredIndex (d := d) p)) := by
  let _ := principalTriangleEquationLayeredIndex_final p he
  exact (Functor.Final.isColimitWhiskerEquiv (principalTriangleEquationLayeredIndex p) t).symm ht

/-- All source principal rings are recovered by models with commuting triangles. -/
def principalTriangleEquationSourceIsColimit (i : ι) :
    IsColimit ((principalLayeredSourceCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) i).whisker
        (principalTriangleEquationLayeredIndex (d := d) p)) :=
  principalTriangleEquationIsColimit p he _ (principalLayeredSourceIsColimit i)

/-- All middle principal rings are recovered by models with commuting triangles. -/
def principalTriangleEquationMiddleIsColimit (j : κ) :
    IsColimit ((principalLayeredMiddleCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) j).whisker
        (principalTriangleEquationLayeredIndex (d := d) p)) :=
  principalTriangleEquationIsColimit p he _ (principalLayeredMiddleIsColimit j)

/-- All final principal rings are recovered by models with commuting triangles. -/
def principalTriangleEquationTargetIsColimit (k : τ) :
    IsColimit ((principalLayeredTargetCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) k).whisker
        (principalTriangleEquationLayeredIndex (d := d) p)) :=
  principalTriangleEquationIsColimit p he _ (principalLayeredTargetIsColimit k)

end FLT.Mazur.FiniteTypeRelationModel

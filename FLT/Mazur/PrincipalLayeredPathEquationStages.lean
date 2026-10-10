/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLayeredPathEquations
public import FLT.Mazur.PrincipalLayeredLimits


/-!
# A cofinal shared index satisfying all path equations

The whole finite-stage coordinate composites agree on this subsystem. All
three levels of original principal charts remain inverse limits after imposing
the equations, with a common middle chart at every stage.
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



variable {ν : τ → Type z} (s : ∀ k, ν k → ι)
  (p q : ∀ k n, PrincipalLayeredPath src mid (s k n) k)


/-- The inherited subsystem of models whose prescribed paths commute. -/
def PrincipalLayeredPathEquationStage :=
  {x : PrincipalLayeredStage src mid a b c f g // PrincipalLayeredPathEquations s p q x}

/-- Path equation models inherit the commuting refinement order. -/
instance principalLayeredPathEquationStagePreorder :
    Preorder (PrincipalLayeredPathEquationStage (a := a) (b := b) (c := c) (f := f) (g := g)
      s p q) := inferInstanceAs (Preorder {x // PrincipalLayeredPathEquations s p q x})

/-- Forget only the path equations, retaining all shared coordinate stages. -/
def principalLayeredPathEquationIndex :
    PrincipalLayeredPathEquationStage (a := a) (b := b) (c := c) (f := f) (g := g) s p q ⥤
      PrincipalLayeredStage src mid a b c f g where
  obj x := x.val
  map h := homOfLE (leOfHom h)

variable [∀ j, Finite (E j)] [∀ k, Finite (F k)]

/-- Common layered refinements preserve the actual path equations. -/
instance principalLayeredPathEquationStageDirected :
    IsDirectedOrder (PrincipalLayeredPathEquationStage
      (a := a) (b := b) (c := c) (f := f) (g := g) s p q) where
  directed x y := by
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x.val y.val
    exact ⟨⟨z, principalLayeredPathEquations_mono s p q x.property hxz⟩, hxz, hyz⟩

variable [∀ k, Finite (ν k)]
  (he : ∀ k n,
    principalLayeredPathMap (a := a) (b := b) (c := c) (f := f) (g := g) (p k n) =
      principalLayeredPathMap (a := a) (b := b) (c := c) (f := f) (g := g) (q k n))

include he in
/-- Equations of original composites cut out a cofinal system of finite-stage models. -/
theorem principalLayeredPathEquationIndex_final :
    (principalLayeredPathEquationIndex (a := a) (b := b) (c := c) (f := f) (g := g)
      s p q).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro x
    obtain ⟨y, hxy, _, hy⟩ := exists_principalLayeredPathEquations s p q he x
    exact ⟨⟨y, hy⟩, ⟨homOfLE hxy⟩⟩
  · intro x y j k
    exact ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

/-- Source rings are recovered while imposing all actual path equations. -/
def principalLayeredPathEquationSourceIsColimit (i : ι) :
    IsColimit ((principalLayeredSourceCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) i).whisker
        (principalLayeredPathEquationIndex s p q)) := by
  let _ := principalLayeredPathEquationIndex_final s p q he
  exact (Functor.Final.isColimitWhiskerEquiv (principalLayeredPathEquationIndex s p q)
    (principalLayeredSourceCocone i)).symm (principalLayeredSourceIsColimit i)

/-- Middle rings are recovered while imposing all actual path equations. -/
def principalLayeredPathEquationMiddleIsColimit (j : κ) :
    IsColimit ((principalLayeredMiddleCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) j).whisker
        (principalLayeredPathEquationIndex s p q)) := by
  let _ := principalLayeredPathEquationIndex_final s p q he
  exact (Functor.Final.isColimitWhiskerEquiv (principalLayeredPathEquationIndex s p q)
    (principalLayeredMiddleCocone j)).symm (principalLayeredMiddleIsColimit j)

/-- Final target rings are recovered while imposing all actual path equations. -/
def principalLayeredPathEquationTargetIsColimit (k : τ) :
    IsColimit ((principalLayeredTargetCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) k).whisker
        (principalLayeredPathEquationIndex s p q)) := by
  let _ := principalLayeredPathEquationIndex_final s p q he
  exact (Functor.Final.isColimitWhiskerEquiv (principalLayeredPathEquationIndex s p q)
    (principalLayeredTargetCocone k)).symm (principalLayeredTargetIsColimit k)

/-- Source spectra remain inverse limits over models with commuting paths. -/
def principalLayeredPathEquationSourceIsLimit (i : ι) :
    IsLimit (Scheme.Spec.mapCone ((principalLayeredSourceCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) i).whisker
        (principalLayeredPathEquationIndex s p q)).op) :=
  isLimitOfPreserves Scheme.Spec (principalLayeredPathEquationSourceIsColimit s p q he i).op

/-- Middle spectra remain inverse limits over models with commuting paths. -/
def principalLayeredPathEquationMiddleIsLimit (j : κ) :
    IsLimit (Scheme.Spec.mapCone ((principalLayeredMiddleCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) j).whisker
        (principalLayeredPathEquationIndex s p q)).op) :=
  isLimitOfPreserves Scheme.Spec (principalLayeredPathEquationMiddleIsColimit s p q he j).op

/-- Final spectra remain inverse limits over models with commuting paths. -/
def principalLayeredPathEquationTargetIsLimit (k : τ) :
    IsLimit (Scheme.Spec.mapCone ((principalLayeredTargetCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) k).whisker
        (principalLayeredPathEquationIndex s p q)).op) :=
  isLimitOfPreserves Scheme.Spec (principalLayeredPathEquationTargetIsColimit s p q he k).op

end FLT.Mazur.FiniteTypeRelationModel

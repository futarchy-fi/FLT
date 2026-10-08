/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalTriangleCofinal


/-!
# Coherent inverse systems of affine triangular diagrams

Direct arrows and their two-edge composites define natural transformations
which agree on the equation subsystem. Every original principal chart is
still the inverse limit of its finite models on this shared index.
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




/-- Direct arrows form a natural transformation between the shared ring systems. -/
def principalTriangleDirectRingMap (k : τ) (e : H k) :
    principalTriangleLayeredIndex (d := d) ⋙
        principalLayeredSourceDiagram (src := src) (mid := mid)
          (a := a) (b := b) (c := c) (f := f) (g := g) (ds k e) ⟶
      principalTriangleLayeredIndex ⋙ principalLayeredTargetDiagram k where
  app x := CommRingCat.ofHom (x.hom k e).toRingHom
  naturality x y h := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (principalBipartite_hom_comm (leOfHom h).2 k e)

variable (p : ∀ k e, PrincipalLayeredPath src mid (ds k e) k)

/-- Composites form a natural transformation on the same source and target systems. -/
def principalTrianglePathRingMap (k : τ) (e : H k) :
    principalTriangleLayeredIndex (d := d) ⋙
        principalLayeredSourceDiagram (src := src) (mid := mid)
          (a := a) (b := b) (c := c) (f := f) (g := g) (ds k e) ⟶
      principalTriangleLayeredIndex ⋙ principalLayeredTargetDiagram k where
  app x := CommRingCat.ofHom (principalLayeredPathHom x.base (p k e)).toRingHom
  naturality x y h := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (principalLayeredPathHom_comm (leOfHom h).1 (p k e))

/-- On commuting triangles the entire direct and composite transformations agree. -/
theorem principalTriangleRingMap_eq (k : τ) (e : H k) :
    Functor.whiskerLeft (principalTriangleEquationIndex (a := a) (b := b) (c := c)
        (f := f) (g := g) (d := d) p) (principalTriangleDirectRingMap k e) =
      Functor.whiskerLeft (principalTriangleEquationIndex p)
        (principalTrianglePathRingMap p k e) := by
  apply NatTrans.ext
  funext x
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (x.property k e)

variable [∀ j, Finite (E j)] [∀ k, Finite (F k)] [∀ k, Finite (H k)]
  (he : ∀ k e, d k e =
    principalLayeredPathMap (a := a) (b := b) (c := c) (f := f) (g := g) (p k e))

/-- Original source spectra are inverse limits over the commuting triangle index. -/
def principalTriangleEquationSourceIsLimit (i : ι) :
    IsLimit (Scheme.Spec.mapCone ((principalLayeredSourceCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) i).whisker
        (principalTriangleEquationLayeredIndex (d := d) p)).op) :=
  isLimitOfPreserves Scheme.Spec (principalTriangleEquationSourceIsColimit p he i).op

/-- Original middle spectra are inverse limits over the commuting triangle index. -/
def principalTriangleEquationMiddleIsLimit (j : κ) :
    IsLimit (Scheme.Spec.mapCone ((principalLayeredMiddleCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) j).whisker
        (principalTriangleEquationLayeredIndex (d := d) p)).op) :=
  isLimitOfPreserves Scheme.Spec (principalTriangleEquationMiddleIsColimit p he j).op

/-- Original final spectra are inverse limits over the commuting triangle index. -/
def principalTriangleEquationTargetIsLimit (k : τ) :
    IsLimit (Scheme.Spec.mapCone ((principalLayeredTargetCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) k).whisker
        (principalTriangleEquationLayeredIndex (d := d) p)).op) :=
  isLimitOfPreserves Scheme.Spec (principalTriangleEquationTargetIsColimit p he k).op

end FLT.Mazur.FiniteTypeRelationModel

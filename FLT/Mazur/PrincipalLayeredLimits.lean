/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLayeredCofinal

public import FLT.Mazur.PrincipalBipartiteLimits

/-!
# Recovering three levels of principal charts on one index

Both coordinate layers are natural transformations between the same three
ring diagrams. In particular, the two occurrences of the middle diagram agree.
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


/-- The source chart rings over the shared two-layer index. -/
def principalLayeredSourceDiagram (i : ι) :
    PrincipalLayeredStage src mid a b c f g ⥤ CommRingCat.{u} :=
  principalLayeredLowerIndex ⋙ principalBipartiteSourceDiagram src a b f i

/-- The common middle chart rings, shared by the two coordinate layers. -/
def principalLayeredMiddleDiagram (j : κ) :
    PrincipalLayeredStage src mid a b c f g ⥤ CommRingCat.{u} :=
  principalLayeredLowerIndex ⋙ principalBipartiteTargetDiagram src a b f j

/-- The final target rings over the shared two-layer index. -/
def principalLayeredTargetDiagram (k : τ) :
    PrincipalLayeredStage src mid a b c f g ⥤ CommRingCat.{u} :=
  principalLayeredUpperIndex ⋙ principalBipartiteTargetDiagram mid b c g k

/-- The outgoing middle diagram is literally the incoming middle diagram. -/
theorem principalLayeredMiddleDiagram_eq (j : κ) :
    principalLayeredMiddleDiagram (src := src) (mid := mid)
        (a := a) (b := b) (c := c) (f := f) (g := g) j =
      principalLayeredUpperIndex ⋙ principalBipartiteSourceDiagram mid b c g j := rfl

/-- Coordinate maps from the first to the second level. -/
def principalLayeredLowerRingMap (j : κ) (e : E j) :
    principalLayeredSourceDiagram (mid := mid) (c := c) (g := g) (src j e) ⟶
      principalLayeredMiddleDiagram (src := src) (a := a) (f := f) j :=
  Functor.whiskerLeft principalLayeredLowerIndex (principalBipartiteRingMap src a b f j e)

/-- Coordinate maps from the second to the third level. -/
def principalLayeredUpperRingMap (k : τ) (e : F k) :
    principalLayeredMiddleDiagram (src := src) (a := a) (f := f) (mid k e) ⟶
      principalLayeredTargetDiagram (mid := mid) (c := c) (g := g) k :=
  Functor.whiskerLeft principalLayeredUpperIndex (principalBipartiteRingMap mid b c g k e)

/-- The source projections have the original localized chart ring as vertex. -/
def principalLayeredSourceCocone (i : ι) :
    Cocone (principalLayeredSourceDiagram (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) i) :=
  (principalBipartiteSourceCocone src a b f i).whisker principalLayeredLowerIndex

/-- The middle projections have the original localized middle ring as vertex. -/
def principalLayeredMiddleCocone (j : κ) :
    Cocone (principalLayeredMiddleDiagram (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) j) :=
  (principalBipartiteTargetCocone src a b f j).whisker principalLayeredLowerIndex

/-- The final projections have the original localized target ring as vertex. -/
def principalLayeredTargetCocone (k : τ) :
    Cocone (principalLayeredTargetDiagram (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) k) :=
  (principalBipartiteTargetCocone mid b c g k).whisker principalLayeredUpperIndex

variable [∀ j, Finite (E j)] [∀ k, Finite (F k)]

/-- The source rings are colimits over the common incidence index. -/
def principalLayeredSourceIsColimit (i : ι) :
    IsColimit (principalLayeredSourceCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) i) :=
  (Functor.Final.isColimitWhiskerEquiv principalLayeredLowerIndex
    (principalBipartiteSourceCocone src a b f i)).symm
      (principalBipartiteSourceIsColimit src a b f i)

/-- The common middle rings are colimits over the common incidence index. -/
def principalLayeredMiddleIsColimit (j : κ) :
    IsColimit (principalLayeredMiddleCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) j) :=
  (Functor.Final.isColimitWhiskerEquiv principalLayeredLowerIndex
    (principalBipartiteTargetCocone src a b f j)).symm
      (principalBipartiteTargetIsColimit src a b f j)

/-- The final rings are colimits over the common incidence index. -/
def principalLayeredTargetIsColimit (k : τ) :
    IsColimit (principalLayeredTargetCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) k) :=
  (Functor.Final.isColimitWhiskerEquiv principalLayeredUpperIndex
    (principalBipartiteTargetCocone mid b c g k)).symm
      (principalBipartiteTargetIsColimit mid b c g k)

/-- Original source principal opens are inverse limits of their shared models. -/
def principalLayeredSourceIsLimit (i : ι) :
    IsLimit (Scheme.Spec.mapCone (principalLayeredSourceCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) i).op) :=
  isLimitOfPreserves Scheme.Spec (principalLayeredSourceIsColimit i).op

/-- Original middle principal opens are inverse limits of their shared models. -/
def principalLayeredMiddleIsLimit (j : κ) :
    IsLimit (Scheme.Spec.mapCone (principalLayeredMiddleCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) j).op) :=
  isLimitOfPreserves Scheme.Spec (principalLayeredMiddleIsColimit j).op

/-- Original final principal opens are inverse limits of their shared models. -/
def principalLayeredTargetIsLimit (k : τ) :
    IsLimit (Scheme.Spec.mapCone (principalLayeredTargetCocone (src := src) (mid := mid)
      (a := a) (b := b) (c := c) (f := f) (g := g) k).op) :=
  isLimitOfPreserves Scheme.Spec (principalLayeredTargetIsColimit k).op

end FLT.Mazur.FiniteTypeRelationModel

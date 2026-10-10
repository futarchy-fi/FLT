/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLayeredPaths

public import FLT.Mazur.PrincipalLayeredDirected

/-!
# Direct arrows alongside two-layer incidence paths

A triangular model adds direct source-to-final arrows to the shared layered
model. All arrows into a final target use the same finite relation set.
-/

@[expose] public noncomputable section

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

/-- A shared two-layer model with additional direct coordinate arrows. -/
structure PrincipalTriangleStage (src : ∀ j, E j → ι) (mid : ∀ k, F k → κ)
    (a : ∀ i, A i) (b : ∀ j, B j) (c : ∀ k, C k)
    (f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j))
    (g : ∀ k e, Localization.Away (b (mid k e)) →ₐ[R] Localization.Away (c k))
    (ds : ∀ k, H k → ι)
    (d : ∀ k e, Localization.Away (a (ds k e)) →ₐ[R] Localization.Away (c k)) where
  /-- The shared two-layer incidence diagram. -/
  base : PrincipalLayeredStage src mid a b c f g
  /-- Direct arrows with the same source and final target stages. -/
  hom : ∀ k e, PrincipalStage R (A (ds k e)) (a (ds k e)) (base.lower.source (ds k e)) →ₐ[R]
    PrincipalStage R (C k) (c k) (base.target k)
  /-- Direct arrows recover their original coordinate maps. -/
  fac : ∀ k e, (principalStageMap R (C k) (c k) (base.target k)).comp (hom k e) =
    (d k e).comp
      (principalStageMap R (A (ds k e)) (a (ds k e)) (base.lower.source (ds k e)))

variable {ds : ∀ k, H k → ι}
  {d : ∀ k e, Localization.Away (a (ds k e)) →ₐ[R] Localization.Away (c k)}

/-- Extract direct arrows as a bipartite diagram with already shared stages. -/
def principalTriangleDirect (x : PrincipalTriangleStage src mid a b c f g ds d) :
    PrincipalBipartiteStage ds a c d where
  source := x.base.lower.source
  target := x.base.target
  hom := x.hom
  fac := x.fac

/-- Refinements commute with both layered paths and direct arrows. -/
instance principalTriangleStagePreorder :
    Preorder (PrincipalTriangleStage src mid a b c f g ds d) where
  le x y := x.base ≤ y.base ∧ principalTriangleDirect x ≤ principalTriangleDirect y
  le_refl x := ⟨le_rfl, le_rfl⟩
  le_trans x y z hxy hyz := ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

/-- Enlarge the common final targets for both kinds of arrows. -/
def principalTriangleTargetExtension (x : PrincipalTriangleStage src mid a b c f g ds d)
    (t : ∀ k, Finset (relationIdeal R (C k))) (ht : x.base.target ≤ t) :
    PrincipalTriangleStage src mid a b c f g ds d where
  base := principalLayeredTargetExtension x.base t ht
  hom k e := (principalTransition (c k) (ht k)).comp (x.hom k e)
  fac k e := (principalBipartiteTargetExtension (principalTriangleDirect x) t ht).fac k e

/-- Final-target extension commutes with every edge of a triangular model. -/
theorem principalTriangleTargetExtension_le (x : PrincipalTriangleStage src mid a b c f g ds d)
    (t : ∀ k, Finset (relationIdeal R (C k))) (ht : x.base.target ≤ t) :
    x ≤ principalTriangleTargetExtension x t ht :=
  ⟨principalLayeredTargetExtension_le x.base t ht,
    principalBipartiteTargetExtension_le (principalTriangleDirect x) t ht⟩

variable [∀ k, Finite (H k)]

/-- Add every direct arrow after enlarging only the final targets of a layered model. -/
theorem exists_principalTriangleStage (x : PrincipalLayeredStage src mid a b c f g) :
    ∃ y : PrincipalTriangleStage src mid a b c f g ds d,
      x ≤ y.base ∧ y.base.lower = x.lower := by
  choose q ht maps hmaps using fun k ↦ exists_principalStageMap_finite_lift (c k)
    (fun e ↦ A (ds k e)) (fun e ↦ a (ds k e)) (d k)
    (fun e ↦ x.lower.source (ds k e)) (x.target k)
  exact ⟨⟨principalLayeredTargetExtension x q ht, maps, hmaps⟩,
    principalLayeredTargetExtension_le x q ht, rfl⟩

end FLT.Mazur.FiniteTypeRelationModel

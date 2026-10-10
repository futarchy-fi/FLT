/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLayeredPaths


/-!
# Finite equations between two-edge coordinate paths

Equations are equalities on the entire current source stage. Surjectivity of
relation transitions makes them persist under refinement, and finite-type
equality detection imposes all equations at each final target simultaneously.
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



variable {ν : τ → Type z} (s : ∀ k, ν k → ι)
  (p q : ∀ k n, PrincipalLayeredPath src mid (s k n) k)

/-- All prescribed composites agree on each current source chart ring. -/
def PrincipalLayeredPathEquations (x : PrincipalLayeredStage src mid a b c f g) : Prop :=
  ∀ k n, principalLayeredPathHom x (p k n) = principalLayeredPathHom x (q k n)

/-- Equalities of full finite-stage composites survive all commuting refinements. -/
theorem principalLayeredPathEquations_mono {x y : PrincipalLayeredStage src mid a b c f g}
    (hx : PrincipalLayeredPathEquations s p q x) (hxy : x ≤ y) :
    PrincipalLayeredPathEquations s p q y := by
  intro k n
  have hs : Function.Surjective (principalTransition (a (s k n)) (hxy.1.1 (s k n))) :=
    FiniteRelationLocalization.transition_surjective R (relationIdeal R (A (s k n)))
      (principalRepresentative R (A (s k n)) (a (s k n))) (hxy.1.1 (s k n))
  apply (AlgHom.cancel_right hs).mp
  rw [principalLayeredPathHom_comm hxy, principalLayeredPathHom_comm hxy, hx k n]

variable [∀ k, Finite (ν k)]

/-- Original path equalities hold at a finite refinement with the lower layer unchanged. -/
theorem exists_principalLayeredPathEquations
    (he : ∀ k n,
      principalLayeredPathMap (a := a) (b := b) (c := c) (f := f) (g := g) (p k n) =
        principalLayeredPathMap (a := a) (b := b) (c := c) (f := f) (g := g) (q k n))
    (x : PrincipalLayeredStage src mid a b c f g) :
    ∃ y : PrincipalLayeredStage src mid a b c f g,
      x ≤ y ∧ y.lower = x.lower ∧ PrincipalLayeredPathEquations s p q y := by
  have hfac (k) (n : ν k) :
      (principalStageMap R (C k) (c k) (x.target k)).comp (principalLayeredPathHom x (p k n)) =
        (principalStageMap R (C k) (c k) (x.target k)).comp
          (principalLayeredPathHom x (q k n)) := by
    rw [principalLayeredPathHom_fac, principalLayeredPathHom_fac, he k n]
  choose t ht hc using fun k ↦ exists_principal_hom_eq_finite (c k)
    (fun n ↦ PrincipalStage R (A (s k n)) (a (s k n)) (x.lower.source (s k n)))
    (x.target k) (fun n ↦ principalLayeredPathHom x (p k n))
    (fun n ↦ principalLayeredPathHom x (q k n)) (hfac k)
  refine ⟨principalLayeredTargetExtension x t ht,
    principalLayeredTargetExtension_le x t ht, rfl, fun k n ↦ ?_⟩
  rw [principalLayeredPathHom_extension, principalLayeredPathHom_extension]
  exact hc k n

end FLT.Mazur.FiniteTypeRelationModel

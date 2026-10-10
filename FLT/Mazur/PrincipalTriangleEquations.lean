/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalTriangleDirected


/-!
# Actual composition equations at finite triangular models

Direct arrows agree with their two-edge paths on the entire source stage.
These equations can all be imposed at the final targets and remain true under
every commuting refinement.
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

variable {ds : ∀ k, H k → ι}
  {d : ∀ k e, Localization.Away (a (ds k e)) →ₐ[R] Localization.Away (c k)}


variable (p : ∀ k e, PrincipalLayeredPath src mid (ds k e) k)

/-- Every direct arrow equals its prescribed two-edge composite. -/
def PrincipalTriangleEquations (x : PrincipalTriangleStage src mid a b c f g ds d) : Prop :=
  ∀ k e, x.hom k e = principalLayeredPathHom x.base (p k e)

/-- Actual triangle commutativity persists on all larger models. -/
theorem principalTriangleEquations_mono {x y : PrincipalTriangleStage src mid a b c f g ds d}
    (hx : PrincipalTriangleEquations p x) (h : x ≤ y) : PrincipalTriangleEquations p y := by
  intro k e
  have hs : Function.Surjective (principalTransition (a (ds k e)) (h.1.1.1 (ds k e))) :=
    FiniteRelationLocalization.transition_surjective R (relationIdeal R (A (ds k e)))
      (principalRepresentative R (A (ds k e)) (a (ds k e))) (h.1.1.1 (ds k e))
  have ht : x.base.target ≤ y.base.target := principalBipartite_target_mono h.1.2
  apply (AlgHom.cancel_right hs).mp
  calc
    (y.hom k e).comp (principalTransition (a (ds k e)) (h.1.1.1 (ds k e))) =
        (principalTransition (c k) (ht k)).comp (x.hom k e) :=
      principalBipartite_hom_comm h.2 k e
    _ = (principalTransition (c k) (ht k)).comp
        (principalLayeredPathHom x.base (p k e)) := by rw [hx k e]
    _ = (principalLayeredPathHom y.base (p k e)).comp
        (principalTransition (a (ds k e)) (h.1.1.1 (ds k e))) :=
      (principalLayeredPathHom_comm h.1 (p k e)).symm

variable [∀ k, Finite (H k)]

/-- All original composition equations hold at a common final-target refinement. -/
theorem exists_principalTriangleEquations
    (he : ∀ k e, d k e =
      principalLayeredPathMap (a := a) (b := b) (c := c) (f := f) (g := g) (p k e))
    (x : PrincipalTriangleStage src mid a b c f g ds d) :
    ∃ y : PrincipalTriangleStage src mid a b c f g ds d,
      x ≤ y ∧ y.base.lower = x.base.lower ∧ PrincipalTriangleEquations p y := by
  have hfac (k) (e : H k) :
      (principalStageMap R (C k) (c k) (x.base.target k)).comp (x.hom k e) =
        (principalStageMap R (C k) (c k) (x.base.target k)).comp
          (principalLayeredPathHom x.base (p k e)) := by
    rw [x.fac, principalLayeredPathHom_fac, he k e]
  choose t ht hc using fun k ↦ exists_principal_hom_eq_finite (c k)
    (fun e ↦ PrincipalStage R (A (ds k e)) (a (ds k e)) (x.base.lower.source (ds k e)))
    (x.base.target k) (x.hom k) (fun e ↦ principalLayeredPathHom x.base (p k e)) (hfac k)
  refine ⟨principalTriangleTargetExtension x t ht,
    principalTriangleTargetExtension_le x t ht, rfl, fun k e ↦ ?_⟩
  change (principalTransition (c k) (ht k)).comp (x.hom k e) =
    principalLayeredPathHom (principalLayeredTargetExtension x.base t ht) (p k e)
  rw [principalLayeredPathHom_extension]
  exact hc k e

end FLT.Mazur.FiniteTypeRelationModel

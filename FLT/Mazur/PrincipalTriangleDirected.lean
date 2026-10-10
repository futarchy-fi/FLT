/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalTriangleStages


/-!
# Common commuting refinements of triangular coordinate models

The lower two-layer diagram is refined first, and equality detection then
makes all direct arrows commute without disturbing the shared middle stages.
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
  [∀ k, Finite (H k)]

/-- Make all direct squares commute over a prescribed layered refinement. -/
theorem exists_principalTriangleStage_compare
    (x z : PrincipalTriangleStage src mid a b c f g ds d) (h : x.base ≤ z.base) :
    ∃ w : PrincipalTriangleStage src mid a b c f g ds d,
      x ≤ w ∧ z ≤ w ∧ w.base.lower = z.base.lower := by
  have hs : x.base.lower.source ≤ z.base.lower.source := h.1.1
  have ht : x.base.target ≤ z.base.target := principalBipartite_target_mono h.2
  have he (k) (e : H k) : (principalStageMap R (C k) (c k) (z.base.target k)).comp
        ((z.hom k e).comp (principalTransition (a (ds k e)) (hs (ds k e)))) =
      (principalStageMap R (C k) (c k) (z.base.target k)).comp
        ((principalTransition (c k) (ht k)).comp (x.hom k e)) := by
    rw [← AlgHom.comp_assoc, z.fac, AlgHom.comp_assoc, principalStageMap_transition,
      ← AlgHom.comp_assoc, principalStageMap_transition, x.fac]
  choose q hq hcomm using fun k ↦ exists_principal_hom_eq_finite (c k)
    (fun e ↦ PrincipalStage R (A (ds k e)) (a (ds k e)) (x.base.lower.source (ds k e)))
    (z.base.target k)
    (fun e ↦ (z.hom k e).comp (principalTransition (a (ds k e)) (hs (ds k e))))
    (fun e ↦ (principalTransition (c k) (ht k)).comp (x.hom k e)) (he k)
  let w := principalTriangleTargetExtension z q hq
  have hzw : z ≤ w := principalTriangleTargetExtension_le z q hq
  refine ⟨w, ⟨h.trans hzw.1, hs, fun k ↦ ⟨fun e ↦ hs (ds k e),
    (ht k).trans (hq k), fun e ↦ ?_⟩⟩, hzw, rfl⟩
  change ((principalTransition (c k) (hq k)).comp (z.hom k e)).comp
    (principalTransition (a (ds k e)) (hs (ds k e))) = _
  rw [AlgHom.comp_assoc, hcomm, ← AlgHom.comp_assoc, principalTransition_comp]
  rfl

/-- Add direct arrows over any layered refinement while preserving old arrows. -/
theorem exists_principalTriangleStage_extension_over
    (x : PrincipalTriangleStage src mid a b c f g ds d)
    (l : PrincipalLayeredStage src mid a b c f g) (h : x.base ≤ l) :
    ∃ y : PrincipalTriangleStage src mid a b c f g ds d,
      x ≤ y ∧ l ≤ y.base ∧ y.base.lower = l.lower := by
  obtain ⟨z, hlz, hz⟩ := exists_principalTriangleStage (ds := ds) (d := d) l
  obtain ⟨y, hxy, hzy, hy⟩ := exists_principalTriangleStage_compare x z (h.trans hlz)
  exact ⟨y, hxy, hlz.trans hzy.1, hy.trans hz⟩

variable [∀ j, Finite (E j)] [∀ k, Finite (F k)]

/-- Any two triangular models have a common commuting refinement. -/
instance principalTriangleStageDirected :
    IsDirectedOrder (PrincipalTriangleStage src mid a b c f g ds d) where
  directed x y := by
    obtain ⟨l, hxl, hyl⟩ := exists_ge_ge x.base y.base
    obtain ⟨z, hxz, hlz, _⟩ := exists_principalTriangleStage_extension_over x l hxl
    obtain ⟨w, hyw, hzw, _⟩ := exists_principalTriangleStage_compare y z (hyl.trans hlz)
    exact ⟨w, hxz.trans hzw, hyw⟩

/-- A triangular coordinate model exists without any equations imposed. -/
instance principalTriangleStageNonempty :
    Nonempty (PrincipalTriangleStage src mid a b c f g ds d) := by
  let x : PrincipalLayeredStage src mid a b c f g := Classical.arbitrary _
  obtain ⟨y, _, _⟩ := exists_principalTriangleStage (ds := ds) (d := d) x
  exact ⟨y⟩

/-- Triangular coordinate models form a filtered category. -/
instance principalTriangleStageFiltered :
    CategoryTheory.IsFiltered (PrincipalTriangleStage src mid a b c f g ds d) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyDirected

/-!
# Finite relations on incoming coordinate families

An existing family can be extended by enlarging only its target. This imposes
any finite set of cone equations witnessed in the original overlap ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {a : ∀ i, A i} {b : B}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b}

/-- Enlarge only the common target of an incoming family. -/
def principalFamilyTargetExtension (x : PrincipalFamilyStage a b f)
    (t : Finset (relationIdeal R B)) (h : x.target ≤ t) : PrincipalFamilyStage a b f where
  source := x.source
  target := t
  hom i := (principalTransition b h).comp (x.hom i)
  fac i := by rw [← AlgHom.comp_assoc, principalStageMap_transition, x.fac]

/-- Target extension is a commuting refinement of the whole family. -/
theorem principalFamilyTargetExtension_le (x : PrincipalFamilyStage a b f)
    (t : Finset (relationIdeal R B)) (h : x.target ≤ t) :
    x ≤ principalFamilyTargetExtension x t h := by
  refine ⟨le_rfl, h, fun i ↦ ?_⟩
  change ((principalTransition b h).comp (x.hom i)).comp
    (principalTransition (a i) (le_refl (x.source i))) = _
  rw [principalTransition_refl, AlgHom.comp_id]
  rfl

/-- All prescribed finite cone equations hold after one common target extension. -/
theorem exists_principalFamilyTargetExtension_relations
    (x : PrincipalFamilyStage a b f) {κ : Type w} [Finite κ]
    (C : κ → Type z) [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
    [∀ k, Algebra.FiniteType R (C k)] (l r : κ → ι)
    (p : ∀ k, C k →ₐ[R] PrincipalStage R (A (l k)) (a (l k)) (x.source (l k)))
    (q : ∀ k, C k →ₐ[R] PrincipalStage R (A (r k)) (a (r k)) (x.source (r k)))
    (h : ∀ k, ((f (l k)).comp
        (principalStageMap R (A (l k)) (a (l k)) (x.source (l k)))).comp (p k) =
      ((f (r k)).comp
        (principalStageMap R (A (r k)) (a (r k)) (x.source (r k)))).comp (q k)) :
    ∃ (t : Finset (relationIdeal R B)) (ht : x.target ≤ t),
      ∀ k, ((principalFamilyTargetExtension x t ht).hom (l k)).comp (p k) =
        ((principalFamilyTargetExtension x t ht).hom (r k)).comp (q k) := by
  have he (k) : (principalStageMap R B b x.target).comp ((x.hom (l k)).comp (p k)) =
      (principalStageMap R B b x.target).comp ((x.hom (r k)).comp (q k)) := by
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, x.fac, x.fac, h]
  obtain ⟨t, ht, hcomm⟩ := exists_principal_hom_eq_finite b C x.target
    (fun k ↦ (x.hom (l k)).comp (p k)) (fun k ↦ (x.hom (r k)).comp (q k)) he
  refine ⟨t, ht, fun k ↦ ?_⟩
  change ((principalTransition b ht).comp (x.hom (l k))).comp (p k) =
    ((principalTransition b ht).comp (x.hom (r k))).comp (q k)
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc]
  exact hcomm k

end FLT.Mazur.FiniteTypeRelationModel

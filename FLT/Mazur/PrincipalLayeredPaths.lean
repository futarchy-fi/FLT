/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLayeredStages

public import FLT.Mazur.PrincipalBipartiteRelations

/-!
# Composites through shared middle charts

Length-two incidence paths have fixed source and target vertices. Their
finite coordinate composites commute with refinement and recover the original
composites. Enlarging only the final targets preserves the lower layer.
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


/-- An incidence path through one middle chart, with prescribed endpoints. -/
structure PrincipalLayeredPath (src : ∀ j, E j → ι) (mid : ∀ k, F k → κ)
    (i : ι) (k : τ) where
  /-- The second incidence. -/
  upper : F k
  /-- The first incidence. -/
  lower : E (mid k upper)
  /-- The starting vertex of the path. -/
  source_eq : src (mid k upper) lower = i

variable {i : ι} {k : τ}

/-- The composite coordinate map of an original two-edge path. -/
def principalLayeredPathMap (p : PrincipalLayeredPath src mid i k) :
    Localization.Away (a i) →ₐ[R] Localization.Away (c k) := by
  rcases p with ⟨e, d, rfl⟩
  exact (g k e).comp (f (mid k e) d)

/-- The composite coordinate map of a two-edge path at one finite stage. -/
def principalLayeredPathHom (x : PrincipalLayeredStage src mid a b c f g)
    (p : PrincipalLayeredPath src mid i k) :
    PrincipalStage R (A i) (a i) (x.lower.source i) →ₐ[R]
      PrincipalStage R (C k) (c k) (x.target k) := by
  rcases p with ⟨e, d, rfl⟩
  exact (x.hom k e).comp (x.lower.hom (mid k e) d)

/-- Path composites recover the original coordinate composites. -/
theorem principalLayeredPathHom_fac (x : PrincipalLayeredStage src mid a b c f g)
    (p : PrincipalLayeredPath src mid i k) :
    (principalStageMap R (C k) (c k) (x.target k)).comp (principalLayeredPathHom x p) =
      (principalLayeredPathMap (a := a) (b := b) (c := c) (f := f) (g := g) p).comp
        (principalStageMap R (A i) (a i) (x.lower.source i)) := by
  rcases p with ⟨e, d, rfl⟩
  change (principalStageMap R (C k) (c k) (x.target k)).comp
    ((x.hom k e).comp (x.lower.hom (mid k e) d)) = _
  rw [← AlgHom.comp_assoc, x.fac, AlgHom.comp_assoc, x.lower.fac, ← AlgHom.comp_assoc]
  rfl

/-- Path composites commute with the common refinement maps. -/
theorem principalLayeredPathHom_comm {x y : PrincipalLayeredStage src mid a b c f g}
    (h : x ≤ y) (p : PrincipalLayeredPath src mid i k) :
    (principalLayeredPathHom y p).comp (principalTransition (a i) (h.1.1 i)) =
      (principalTransition (c k) (principalBipartite_target_mono h.2 k)).comp
        (principalLayeredPathHom x p) := by
  rcases p with ⟨e, d, rfl⟩
  change ((y.hom k e).comp (y.lower.hom (mid k e) d)).comp
    (principalTransition (a (src (mid k e) d)) (h.1.1 (src (mid k e) d))) = _
  rw [AlgHom.comp_assoc, principalBipartite_hom_comm h.1, ← AlgHom.comp_assoc]
  have he := principalBipartite_hom_comm h.2 k e
  change (y.hom k e).comp
    (principalTransition (b (mid k e)) (principalBipartite_target_mono h.1 (mid k e))) =
      (principalTransition (c k) (principalBipartite_target_mono h.2 k)).comp (x.hom k e) at he
  rw [he]
  rfl

/-- Extend final targets without changing any lower chart or middle stage. -/
def principalLayeredTargetExtension (x : PrincipalLayeredStage src mid a b c f g)
    (t : ∀ k, Finset (relationIdeal R (C k))) (ht : x.target ≤ t) :
    PrincipalLayeredStage src mid a b c f g where
  lower := x.lower
  target := t
  hom k e := (principalTransition (c k) (ht k)).comp (x.hom k e)
  fac k e := by rw [← AlgHom.comp_assoc, principalStageMap_transition, x.fac]

/-- Final-target extension is a commuting refinement in both layers. -/
theorem principalLayeredTargetExtension_le (x : PrincipalLayeredStage src mid a b c f g)
    (t : ∀ k, Finset (relationIdeal R (C k))) (ht : x.target ≤ t) :
    x ≤ principalLayeredTargetExtension x t ht :=
  ⟨le_rfl, principalBipartiteTargetExtension_le (principalLayeredUpper x) t ht⟩

/-- Path maps after final-target extension are obtained by postcomposition. -/
theorem principalLayeredPathHom_extension (x : PrincipalLayeredStage src mid a b c f g)
    (t : ∀ k, Finset (relationIdeal R (C k))) (ht : x.target ≤ t)
    (p : PrincipalLayeredPath src mid i k) :
    principalLayeredPathHom (principalLayeredTargetExtension x t ht) p =
      (principalTransition (c k) (ht k)).comp (principalLayeredPathHom x p) := by
  rcases p with ⟨e, d, rfl⟩
  exact AlgHom.comp_assoc _ _ _

end FLT.Mazur.FiniteTypeRelationModel

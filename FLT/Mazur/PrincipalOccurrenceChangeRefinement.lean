/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCoordinateChanges

/-!
# Coordinate changes commute with refinement

The full transition square for a change between two incident charts follows
from their shared target square. Thus the identity, inverse and cocycle maps
are compatible with the finite-relation inverse system.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  {x y : PrincipalOccurrenceStage dst a b f}

/-- Every reindexed incoming square retains the prescribed shared target transition. -/
theorem principalOccurrenceIncomingHom_comm (hxy : x ≤ y) (j : κ)
    (e : PrincipalIncoming (dst := dst) j) :
    (principalOccurrenceIncomingHom y j e).comp
      (principalTransition (a e.val.1 e.val.2) (principalOccurrence_source_mono hxy e.val.1)) =
    (principalTransition (b j) (principalOccurrence_target_mono hxy j)).comp
      (principalOccurrenceIncomingHom x j e) := by
  obtain ⟨⟨i, k⟩, rfl⟩ := e
  exact principalOccurrence_hom_comm hxy i k

/-- Chart-change identifications commute on the entire finite principal source ring. -/
theorem principalOccurrenceCoordinateChange_comm
    (hx : ∀ i e, Function.Bijective (x.hom i e))
    (hy : ∀ i e, Function.Bijective (y.hom i e)) (hxy : x ≤ y) (j : κ)
    (e d : PrincipalIncoming (dst := dst) j) :
    (principalOccurrenceCoordinateChange y hy j e d).toAlgHom.comp
      (principalTransition (a e.val.1 e.val.2) (principalOccurrence_source_mono hxy e.val.1)) =
    (principalTransition (a d.val.1 d.val.2) (principalOccurrence_source_mono hxy d.val.1)).comp
      (principalOccurrenceCoordinateChange x hx j e d).toAlgHom := by
  have hinj : Function.Injective (principalOccurrenceIncomingHom y j d) := by
    rw [← principalOccurrenceIncomingEquiv_hom y hy j d]
    exact (principalOccurrenceIncomingEquiv y hy j d).injective
  apply (AlgHom.cancel_left hinj).mp
  rw [← AlgHom.comp_assoc, principalOccurrenceCoordinateChange_fac,
    principalOccurrenceIncomingHom_comm hxy, ← AlgHom.comp_assoc,
    principalOccurrenceIncomingHom_comm hxy, AlgHom.comp_assoc,
    principalOccurrenceCoordinateChange_fac]

end FLT.Mazur.FiniteTypeRelationModel

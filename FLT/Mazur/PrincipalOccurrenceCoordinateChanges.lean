/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceDirected

/-!
# Coordinate changes through a shared overlap target

Bijective occurrence maps identify principal opens in different ambient
charts with the same overlap ring. These explicit coordinate changes satisfy
identity, inverse and three-chart composition equations on the full rings.
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
  (x : PrincipalOccurrenceStage dst a b f) (hx : ∀ i e, Function.Bijective (x.hom i e))

/-- Each incoming principal ring has its actual coordinate equivalence to the shared target. -/
def principalOccurrenceIncomingEquiv (j : κ) (e : PrincipalIncoming (dst := dst) j) :
    PrincipalStage R (A e.val.1) (a e.val.1 e.val.2) (x.source e.val.1) ≃ₐ[R]
      PrincipalStage R (B j) (b j) (x.target j) := by
  obtain ⟨⟨i, k⟩, rfl⟩ := e
  exact AlgEquiv.ofBijective (x.hom i k) (hx i k)

/-- The equivalence uses exactly the given incoming coordinate map. -/
theorem principalOccurrenceIncomingEquiv_hom (j : κ) (e : PrincipalIncoming (dst := dst) j) :
    (principalOccurrenceIncomingEquiv x hx j e).toAlgHom =
      principalOccurrenceIncomingHom x j e := by
  obtain ⟨⟨i, k⟩, rfl⟩ := e
  rfl

/-- Change charts through the common overlap, with no independent target choices. -/
def principalOccurrenceCoordinateChange (j : κ) (e d : PrincipalIncoming (dst := dst) j) :
    PrincipalStage R (A e.val.1) (a e.val.1 e.val.2) (x.source e.val.1) ≃ₐ[R]
      PrincipalStage R (A d.val.1) (a d.val.1 d.val.2) (x.source d.val.1) :=
  (principalOccurrenceIncomingEquiv x hx j e).trans
    (principalOccurrenceIncomingEquiv x hx j d).symm

/-- A coordinate change preserves the map into the shared overlap ring. -/
theorem principalOccurrenceCoordinateChange_fac (j : κ)
    (e d : PrincipalIncoming (dst := dst) j) :
    (principalOccurrenceIncomingHom x j d).comp
      (principalOccurrenceCoordinateChange x hx j e d).toAlgHom =
        principalOccurrenceIncomingHom x j e := by
  rw [← principalOccurrenceIncomingEquiv_hom x hx j d,
    ← principalOccurrenceIncomingEquiv_hom x hx j e]
  apply DFunLike.ext
  intro z
  exact (principalOccurrenceIncomingEquiv x hx j d).apply_symm_apply _

/-- Changing a chart to itself is the identity on its entire principal ring. -/
theorem principalOccurrenceCoordinateChange_refl (j : κ)
    (e : PrincipalIncoming (dst := dst) j) :
    principalOccurrenceCoordinateChange x hx j e e = AlgEquiv.refl := by
  apply DFunLike.ext
  intro z
  exact (principalOccurrenceIncomingEquiv x hx j e).symm_apply_apply z

/-- The reversed coordinate change is the exact inverse. -/
theorem principalOccurrenceCoordinateChange_symm (j : κ)
    (e d : PrincipalIncoming (dst := dst) j) :
    (principalOccurrenceCoordinateChange x hx j e d).symm =
      principalOccurrenceCoordinateChange x hx j d e := rfl

/-- Three incoming charts satisfy the full cocycle equation through their shared overlap. -/
theorem principalOccurrenceCoordinateChange_comp (j : κ)
    (e d c : PrincipalIncoming (dst := dst) j) :
    (principalOccurrenceCoordinateChange x hx j d c).toAlgHom.comp
      (principalOccurrenceCoordinateChange x hx j e d).toAlgHom =
        (principalOccurrenceCoordinateChange x hx j e c).toAlgHom := by
  apply DFunLike.ext
  intro z
  change (principalOccurrenceIncomingEquiv x hx j c).symm
    ((principalOccurrenceIncomingEquiv x hx j d)
      ((principalOccurrenceIncomingEquiv x hx j d).symm
        ((principalOccurrenceIncomingEquiv x hx j e) z))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

end FLT.Mazur.FiniteTypeRelationModel

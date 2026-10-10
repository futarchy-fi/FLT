/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanStages
public import FLT.Mazur.FiniteRelationPrincipalPathQuotients

/-!
# Fixed-target fan isomorphisms from restriction paths

Restriction maps into the explicitly localized target rings and their full
ambient equations suffice. Kernel compatibility is a consequence of these
paths, rather than a separate hypothesis on ideals.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  {a : ι → A} {b : ∀ i, B i}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away (b i)}

/-- The overlap target as a genuine localization in the second leg's coordinates. -/
abbrev PrincipalFanRestrictionTarget (x : PrincipalFanStage a b f) (i j : ι) :=
  Localization.Away (x.hom j (FiniteRelationLocalization.numerator (relationIdeal R A)
    (principalRepresentative R A (a j)) x.source (principalRepresentative R A (a i))))

/-- Equations of restriction paths on the full shared ambient chart stage. -/
def PrincipalFanRestrictionEquations (x : PrincipalFanStage a b f)
    (ρ : ∀ i j, PrincipalStage R (B i) (b i) (x.target i) →+*
      PrincipalFanRestrictionTarget x i j) : Prop :=
  ∀ i j, ((ρ i j).comp (x.hom i).toRingHom).comp
      (algebraMap (Stage R A x.source) (PrincipalStage R A (a i) x.source)) =
    ((algebraMap (PrincipalStage R (B j) (b j) (x.target j))
      (PrincipalFanRestrictionTarget x i j)).comp (x.hom j).toRingHom).comp
        (algebraMap (Stage R A x.source) (PrincipalStage R A (a j) x.source))

variable [Finite ι]

/-- Refine one ambient relation set to isomorphisms with all prescribed targets fixed. -/
theorem exists_principalFan_equivs_of_paths (hf : ∀ i, Function.Injective (f i))
    (x : PrincipalFanStage a b f) (hx : ∀ i, Function.Surjective (x.hom i))
    (ρ : ∀ i j, PrincipalStage R (B i) (b i) (x.target i) →+*
      PrincipalFanRestrictionTarget x i j) (hρ : PrincipalFanRestrictionEquations x ρ) :
    ∃ (q : Finset (relationIdeal R A)) (hsq : x.source ≤ q)
      (d : ∀ i, PrincipalStage R A (a i) q ≃ₐ[R]
        PrincipalStage R (B i) (b i) (x.target i)),
      (∀ i, (d i).toAlgHom.comp (principalTransition (a i) hsq) = x.hom i) ∧
      (∀ i, (principalStageMap R (B i) (b i) (x.target i)).comp (d i).toAlgHom =
        (f i).comp (principalStageMap R A (a i) q)) := by
  have hk (i) : RingHom.ker (x.hom i).toRingHom ≤
      RingHom.ker (FiniteRelationLocalization.toQuotient R (relationIdeal R A)
        (principalRepresentative R A (a i)) x.source).toRingHom := by
    intro z hz
    change x.hom i z = 0 at hz
    apply (principalQuotientEquiv R A (a i)).injective
    change principalStageMap R A (a i) x.source z = principalQuotientEquiv R A (a i) 0
    rw [map_zero]
    apply hf i
    rw [← AlgHom.comp_apply, ← x.fac i, AlgHom.comp_apply, hz, map_zero, map_zero]
  obtain ⟨q, hsq, d, hd⟩ :=
    FiniteRelationLocalization.exists_shared_quotient_equivs_of_principal_paths R
      (relationIdeal R A) (fun i ↦ principalRepresentative R A (a i))
      x.source x.hom hx hk ρ hρ
  refine ⟨q, hsq, d, hd, fun i ↦ ?_⟩
  apply (AlgHom.cancel_right (FiniteRelationLocalization.transition_surjective R
    (relationIdeal R A) (principalRepresentative R A (a i)) hsq)).mp
  rw [AlgHom.comp_assoc, hd, x.fac, AlgHom.comp_assoc, principalStageMap_transition]

end FLT.Mazur.FiniteTypeRelationModel

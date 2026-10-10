/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanRefinedRestrictionTargets
public import FLT.Mazur.PrincipalFanRestrictionUniqueness

/-!
# Original recovery of finite restriction maps

Original chart isomorphisms construct restriction maps to the actual double
open. When old coordinates are surjective, their ambient equations force
every finite restriction to recover this original map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

/-- Map a principal localization along an algebra map before specializing its rings. -/
def principalRestrictionProjectionMap {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) (d : S) :
    Localization.Away d →ₐ[R] Localization.Away (f d) :=
  IsLocalization.Away.mapₐ _ _ f d

/-- The generic principal localization map preserves the specified numerators. -/
theorem principalRestrictionProjectionMap_algebraMap {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (d z : S) :
    principalRestrictionProjectionMap f d (algebraMap S (Localization.Away d) z) =
      algebraMap T (Localization.Away (f d)) (f z) := by
  simp [principalRestrictionProjectionMap, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)] {a : ι → A} {b : ∀ i, B i}
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))

/-- The actual original double open in the target's quotient presentation. -/
abbrev PrincipalFanOriginalTarget
    (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)) (i j : ι) :=
  FiniteRelationIterated.Quotient R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j)
    (principalFanRestrictionDenominator x i j)

/-- Construct the original restriction from the inverse of the source chart isomorphism. -/
def principalFanOriginalRestriction
    (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)) (i j : ι) :
    Localization.Away (b i) →ₐ[R] PrincipalFanOriginalTarget e x i j :=
  (PrincipalOriginalRestrictionPaths.exists_restriction_at (a i) (e i)
    (principalFanOriginalAmbient (f := fun i ↦ (e i).toAlgHom) j) _
    (principalFanRestrictionDenominator_spec x i j)).choose

/-- Original restrictions satisfy the ambient chart equation. -/
theorem principalFanOriginalRestriction_ambient
    (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)) (i j : ι) :
    (principalFanOriginalRestriction e x i j).comp
      ((e i).toAlgHom.comp (Algebra.algHom R A (Localization.Away (a i)))) =
    (Algebra.algHom R _ (PrincipalFanOriginalTarget e x i j)).comp
      (principalFanOriginalAmbient (f := fun i ↦ (e i).toAlgHom) j) :=
  (PrincipalOriginalRestrictionPaths.exists_restriction_at (a i) (e i)
    (principalFanOriginalAmbient (f := fun i ↦ (e i).toAlgHom) j) _
    (principalFanRestrictionDenominator_spec x i j)).choose_spec

/-- Project the canonical finite double open onto its original double open. -/
def principalFanRestrictionProjection
    (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)) (i j : ι) :
    PrincipalFanRestrictionTarget x i j →ₐ[R] PrincipalFanOriginalTarget e x i j :=
  principalRestrictionProjectionMap
    (FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j))
    (principalFanRestrictionDenominator x i j)

/-- Projection on double-open numerators is the usual quotient projection. -/
theorem principalFanRestrictionProjection_algebraMap
    (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)) (i j : ι)
    (z : PrincipalStage R (B j) (b j) (x.target j)) :
    principalFanRestrictionProjection e x i j (algebraMap _ _ z) =
      algebraMap _ (PrincipalFanOriginalTarget e x i j)
        (FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
          (principalRepresentative R (B j) (b j)) (x.target j) z) := by
  exact principalRestrictionProjectionMap_algebraMap _ _ z

/-- Ambient equations recover original restrictions without adding a recovery hypothesis. -/
theorem principalFanRestriction_original_recovery
    {x y : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)} (h : x ≤ y) (i j : ι)
    (hx : Function.Surjective (x.hom i))
    (ρ : PrincipalStage R (B i) (b i) (x.target i) →ₐ[R] PrincipalFanRestrictionTarget y i j)
    (hρ : ρ.comp (principalFanAmbient x i) =
      (principalFanRestrictionInclusion y i j).comp
        ((principalTransition (b j) (principalFan_target_mono h j)).comp
          (principalFanAmbient x j))) :
    (principalFanRestrictionProjection e y i j).comp ρ =
      (principalFanOriginalRestriction e y i j).comp
        (principalStageMap R (B i) (b i) (x.target i)) := by
  apply principalFan_restriction_ext x i hx
  rw [AlgHom.comp_assoc, hρ, AlgHom.comp_assoc, principalFanAmbient_fac,
    ← AlgHom.comp_assoc (principalFanOriginalRestriction e y i j),
    principalFanOriginalRestriction_ambient]
  apply AlgHom.ext
  intro z
  change principalFanRestrictionProjection e y i j
    (algebraMap (PrincipalStage R (B j) (b j) (y.target j)) _
      (principalTransition (b j) (principalFan_target_mono h j) (principalFanAmbient x j z))) = _
  rw [principalFanRestrictionProjection_algebraMap]
  have ht := AlgHom.congr_fun
    (FiniteRelationLocalization.toQuotient_comp R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (principalFan_target_mono h j))
    (principalFanAmbient x j z)
  have ha := AlgHom.congr_fun (principalFanAmbient_quotient x j) z
  exact congrArg (algebraMap _ (PrincipalFanOriginalTarget e y i j)) (ht.trans ha)

end FLT.Mazur.FiniteTypeRelationModel

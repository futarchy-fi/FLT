/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanRefinedRestrictionPaths

/-!
# Actual transition maps between fan restriction targets

The comparison with literal old-coordinate targets constructs restriction
transitions. They preserve all numerators and compose on the full localized
rings, giving the target maps needed to transport path equations.
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
  {x y z : PrincipalFanStage a b f}

/-- The actual map between restriction targets induced by a fan refinement. -/
def principalFanRestrictionTransition (h : x ≤ y) (i j : ι) :
    PrincipalFanRestrictionTarget x i j →ₐ[R] PrincipalFanRestrictionTarget y i j := by
  let _ : IsLocalization.Away
      (principalTransition (b j) (principalFan_target_mono h j)
        (principalFanRestrictionDenominator x i j)) (PrincipalFanRestrictionTarget y i j) :=
    principalFanRefinedRestrictionTarget_isLocalization h i j
  let _ : IsLocalization.Away (principalFanRestrictionDenominator x i j)
      (PrincipalFanRestrictionTarget x i j) :=
    inferInstanceAs (IsLocalization.Away (principalFanRestrictionDenominator x i j)
      (Localization.Away (principalFanRestrictionDenominator x i j)))
  exact IsLocalization.Away.mapₐ _ _
    (principalTransition (b j) (principalFan_target_mono h j))
    (principalFanRestrictionDenominator x i j)

/-- Restriction transitions preserve every numerator with its actual chart transition. -/
theorem principalFanRestrictionTransition_algebraMap (h : x ≤ y) (i j : ι)
    (q : PrincipalStage R (B j) (b j) (x.target j)) :
    principalFanRestrictionTransition h i j (algebraMap _ _ q) =
      algebraMap _ (PrincipalFanRestrictionTarget y i j)
        (principalTransition (b j) (principalFan_target_mono h j) q) := by
  simp [principalFanRestrictionTransition, IsLocalization.Away.mapₐ,
    IsLocalization.Away.map]

/-- Reflexive target transitions are identities on the full double localization. -/
theorem principalFanRestrictionTransition_refl (x : PrincipalFanStage a b f) (i j : ι) :
    principalFanRestrictionTransition (le_refl x) i j =
      AlgHom.id R (PrincipalFanRestrictionTarget x i j) := by
  apply IsLocalization.algHom_ext (Submonoid.powers
    (x.hom j (FiniteRelationLocalization.numerator (relationIdeal R A)
      (principalRepresentative R A (a j)) x.source (principalRepresentative R A (a i)))))
  apply DFunLike.ext
  intro q
  change principalFanRestrictionTransition (le_refl x) i j (algebraMap _ _ q) = _
  rw [principalFanRestrictionTransition_algebraMap]
  change algebraMap _ _ (principalTransition (b j) (le_refl (x.target j)) q) = _
  rw [principalTransition_refl]
  rfl

/-- Target transitions compose on all fractions, not only on their ambient numerators. -/
theorem principalFanRestrictionTransition_comp (h : x ≤ y) (k : y ≤ z) (i j : ι) :
    (principalFanRestrictionTransition k i j).comp (principalFanRestrictionTransition h i j) =
      principalFanRestrictionTransition (h.trans k) i j := by
  apply IsLocalization.algHom_ext (Submonoid.powers
    (x.hom j (FiniteRelationLocalization.numerator (relationIdeal R A)
      (principalRepresentative R A (a j)) x.source (principalRepresentative R A (a i)))))
  apply DFunLike.ext
  intro q
  change principalFanRestrictionTransition k i j
    (principalFanRestrictionTransition h i j (algebraMap _ _ q)) =
      principalFanRestrictionTransition (h.trans k) i j (algebraMap _ _ q)
  rw [principalFanRestrictionTransition_algebraMap,
    principalFanRestrictionTransition_algebraMap,
    principalFanRestrictionTransition_algebraMap]
  exact congrArg (algebraMap _ (PrincipalFanRestrictionTarget z i j))
    (AlgHom.congr_fun (principalTransition_comp (b j)
      (principalFan_target_mono h j) (principalFan_target_mono k j)) q)

/-- Commuting restriction squares transport old path equations to the full refined rings. -/
theorem principalFanRestrictionEquations_of_refinement (h : x ≤ y)
    (ρx : ∀ i j, PrincipalStage R (B i) (b i) (x.target i) →ₐ[R]
      PrincipalFanRestrictionTarget x i j)
    (ρy : ∀ i j, PrincipalStage R (B i) (b i) (y.target i) →ₐ[R]
      PrincipalFanRestrictionTarget y i j)
    (hρx : PrincipalFanRestrictionEquations x (fun i j ↦ (ρx i j).toRingHom))
    (hsq : ∀ i j,
      (ρy i j).comp (principalTransition (b i) (principalFan_target_mono h i)) =
        (principalFanRestrictionTransition h i j).comp (ρx i j)) :
    PrincipalFanRestrictionEquations y (fun i j ↦ (ρy i j).toRingHom) := by
  have he (i j) : (ρy i j).comp (principalFanAmbient y i) =
      (principalFanRestrictionInclusion y i j).comp (principalFanAmbient y j) := by
    apply AlgHom.ext
    intro z
    obtain ⟨q, rfl⟩ := FiniteRelationModel.transition_surjective R (relationIdeal R A) h.1 z
    have hi := AlgHom.congr_fun (principalFanAmbient_refinement h i) q
    have hj := AlgHom.congr_fun (principalFanAmbient_refinement h j) q
    have hs := AlgHom.congr_fun (hsq i j) (principalFanAmbient x i q)
    have hp := RingHom.congr_fun (hρx i j) q
    change ρx i j (principalFanAmbient x i q) =
      algebraMap _ (PrincipalFanRestrictionTarget x i j) (principalFanAmbient x j q) at hp
    exact (congrArg (ρy i j) hi).trans (hs.trans
      ((congrArg (principalFanRestrictionTransition h i j) hp).trans
        ((principalFanRestrictionTransition_algebraMap h i j _).trans
          (congrArg (algebraMap _ (PrincipalFanRestrictionTarget y i j)) hj.symm))))
  intro i j
  exact congrArg AlgHom.toRingHom (he i j)

end FLT.Mazur.FiniteTypeRelationModel

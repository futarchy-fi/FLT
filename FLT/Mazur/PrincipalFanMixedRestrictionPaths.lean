/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanInitialRestrictionTransition

/-!
# Transport canonical restrictions to a later literal target

The old restriction source can precede the shared intermediate stage.
Surjective ambient transitions and numerator transport turn its retained
square into the exact path equation required for kernel patching.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)] {a : ι → A} {b : ∀ i, B i}
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))


attribute [local irreducible] principalFanInitialRestrictionTransition
  FiniteRelationIterated.transition FiniteRelationLocalization.transition

variable {x y z : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)}

/-- Earlier-source squares carry ambient paths to the shared refined restriction domain. -/
theorem principalFanMixedRestriction_path (hxy : x ≤ y) (hyz : y ≤ z) (i j : ι)
    (ρ : PrincipalStage R (B i) (b i) (x.target i) →ₐ[R]
      PrincipalFanRestrictionTarget y i j)
    (σ : PrincipalStage R (B i) (b i) (z.target i) →ₐ[R]
      PrincipalFanOldRestrictionTarget hyz i j)
    (hOld : σ.comp (principalTransition (b i)
        ((principalFan_target_mono hxy i).trans (principalFan_target_mono hyz i))) =
      (principalFanInitialRestrictionTransition e hyz i j).comp ρ)
    (hρ : ρ.comp (principalFanAmbient x i) =
      (principalFanRestrictionInclusion y i j).comp
        ((principalTransition (b j) (principalFan_target_mono hxy j)).comp
          (principalFanAmbient x j))) :
    (σ.comp (principalTransition (b i) (principalFan_target_mono hyz i))).comp
      (principalFanAmbient y i) =
    (principalFanOldRestrictionInclusion hyz i j).comp
      ((principalTransition (b j) (principalFan_target_mono hyz j)).comp
        (principalFanAmbient y j)) := by
  apply AlgHom.ext
  intro v
  obtain ⟨w, rfl⟩ :=
    FiniteRelationModel.transition_surjective R (relationIdeal R A) hxy.1 v
  have hi := AlgHom.congr_fun (principalFanAmbient_refinement hxy i) w
  have hj := AlgHom.congr_fun (principalFanAmbient_refinement hxy j) w
  have hold := AlgHom.congr_fun hOld (principalFanAmbient x i w)
  have hr := AlgHom.congr_fun hρ w
  have ht := AlgHom.congr_fun
    (principalTransition_comp (b i) (principalFan_target_mono hxy i)
      (principalFan_target_mono hyz i)) (principalFanAmbient x i w)
  change σ (principalTransition (b i) _ (principalFanAmbient y i _)) =
    algebraMap (PrincipalStage R (B j) (b j) (z.target j)) _
      (principalTransition (b j) (principalFan_target_mono hyz j) (principalFanAmbient y j _))
  change principalFanAmbient y i _ = principalTransition (b i) _
    (principalFanAmbient x i w) at hi
  change principalFanAmbient y j _ = principalTransition (b j) _
    (principalFanAmbient x j w) at hj
  change σ (principalTransition (b i) _ _) =
    principalFanInitialRestrictionTransition e hyz i j (ρ (principalFanAmbient x i w)) at hold
  change ρ (principalFanAmbient x i w) =
    algebraMap (PrincipalStage R (B j) (b j) (y.target j)) _
      (principalTransition (b j) (principalFan_target_mono hxy j)
        (principalFanAmbient x j w)) at hr
  have hnum := principalFanInitialRestrictionTransition_algebraMap e hyz i j
    (principalTransition (b j) (principalFan_target_mono hxy j) (principalFanAmbient x j w))
  exact (congrArg (fun v ↦ σ (principalTransition (b i)
    (principalFan_target_mono hyz i) v)) hi).trans
      ((congrArg σ ht).trans (hold.trans
        ((congrArg (principalFanInitialRestrictionTransition e hyz i j) hr).trans
          (hnum.trans (congrArg (fun v ↦ algebraMap
            (PrincipalStage R (B j) (b j) (z.target j))
            (PrincipalFanOldRestrictionTarget hyz i j)
            (principalTransition (b j) (principalFan_target_mono hyz j) v)) hj.symm)))))

end FLT.Mazur.FiniteTypeRelationModel

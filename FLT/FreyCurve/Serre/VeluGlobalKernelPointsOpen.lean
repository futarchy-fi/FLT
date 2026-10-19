/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluTranslatedSimpleFiber

/-!
# Every original subgroup point is open in the full Vélu kernel

These are sections of the actual scheme-theoretic fiber. The open immersion
assertion uses translated exact fibers, so detects its local scheme structure.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- An original subgroup point as a section of the full scheme-theoretic kernel. -/
def veluGlobalKernelPoint (P : G) : Spec (.of K) ⟶ veluGlobalKernel E G hodd :=
  pullback.lift (affineSmoothPoint E P.val ≫ (integralSmoothOpen E).ι) (𝟙 _)
    (by simpa using veluGlobalMorphism_kernel E G hodd P.val P.property)

/-- Its source projection is precisely the original point of the original cubic. -/
@[reassoc] theorem veluGlobalKernelPoint_fst (P : G) :
    veluGlobalKernelPoint E G hodd P ≫ pullback.fst _ _ =
      affineSmoothPoint E P.val ≫ (integralSmoothOpen E).ι :=
  pullback.lift_fst _ _ _

/-- Each original subgroup point is a section over the original field. -/
@[reassoc] theorem veluGlobalKernelPoint_snd (P : G) :
    veluGlobalKernelPoint E G hodd P ≫ pullback.snd _ _ = 𝟙 (Spec (.of K)) :=
  pullback.lift_snd _ _ _

/-- The original subgroup identity gives the previously constructed kernel identity. -/
theorem veluGlobalKernelPoint_zero :
    veluGlobalKernelPoint E G hodd 0 = veluGlobalKernelZero E G hodd := by
  apply pullback.hom_ext
  · rw [veluGlobalKernelPoint_fst, veluGlobalKernelZero, pullback.lift_fst]
    change affineSmoothPoint E (0 : (E.map (algebraMap K K)).toAffine.Point) ≫ _ = _
    rw [affineSmoothPoint_zero]
    change Spec.map (𝟙 (CommRingCat.of K)) ≫ _ = _
    rw [Spec.map_id, Category.id_comp]
  · rw [veluGlobalKernelPoint_snd, veluGlobalKernelZero, pullback.lift_snd]

/-- Every negative original nonzero subgroup section is open in the actual kernel. -/
theorem veluGlobalKernelPoint_negative_isOpenImmersion {u v : K}
    (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∈ G) :
    IsOpenImmersion (veluGlobalKernelPoint E G hodd (-⟨.some u v hQ, hQG⟩)) := by
  apply FLT.Mazur.OpenFiberSection.isOpenImmersion
    (veluTranslatedSimpleOpenImmersion E G (.some u v hQ))
    (veluGlobalMorphism E G hodd) (integralCurveZero (curve E G))
    (veluSimplePointLift E G)
  · rw [veluTranslatedSimplePoint_source, veluGlobalKernelPoint_fst]
    rfl
  · exact veluGlobalKernelPoint_snd E G hodd _
  · exact veluTranslatedSimple_identityFiber E G hodd hQ hQG

/-- Each point of the original subgroup is an actual open immersion into the full fiber. -/
instance veluGlobalKernelPoint_isOpenImmersion (P : G) :
    IsOpenImmersion (veluGlobalKernelPoint E G hodd P) := by
  have h (Q : G) : IsOpenImmersion (veluGlobalKernelPoint E G hodd (-Q)) := by
    obtain ⟨Q, hQ⟩ := Q
    cases Q with
    | zero =>
      have hz : -(⟨0, hQ⟩ : G) = 0 := by ext; simp
      change IsOpenImmersion (veluGlobalKernelPoint E G hodd (-(⟨0, hQ⟩ : G)))
      rw [hz, veluGlobalKernelPoint_zero]
      infer_instance
    | some u v hQ' =>
      exact veluGlobalKernelPoint_negative_isOpenImmersion E G hodd hQ' hQ
  simpa only [neg_neg] using h (-P)

end WeierstrassCurve.Velu

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffinePointInjective
public import FLT.FreyCurve.Serre.VeluGlobalKernelEtale

/-!
# The full original kernel has the cardinality and length of the original subgroup

The equivalence is evaluation of the original subgroup sections, so the
length calculation retains their original points and the full scheme fiber.
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

/-- Original subgroup sections retain their distinct labels in the actual fiber. -/
theorem veluGlobalKernelPoint_injective :
    Function.Injective (veluGlobalKernelPoint E G hodd) := by
  intro P Q h
  apply Subtype.ext
  apply affineSmoothPoint_inclusion_injective E
  simpa only [veluGlobalKernelPoint_fst] using
    congrArg (fun f ↦ f ≫ pullback.fst (veluGlobalMorphism E G hodd)
      (integralCurveZero (curve E G))) h

/-- Evaluation gives a bijection from the original subgroup onto all scheme points. -/
theorem veluGlobalKernelPoint_bijective :
    Function.Bijective (fun P : G ↦
      veluGlobalKernelPoint E G hodd P (IsLocalRing.closedPoint K)) := by
  constructor
  · intro P Q h
    apply veluGlobalKernelPoint_injective E G hodd
    exact ext_of_apply_closedPoint_eq (pullback.snd _ _)
      (veluGlobalKernelPoint_snd E G hodd P) (veluGlobalKernelPoint_snd E G hodd Q) h
  · intro x
    have hx : x ∈ ⨆ P : G, (veluGlobalKernelPoint E G hodd P).opensRange := by
      rw [veluGlobalKernelPoint_iSup_eq_top]
      trivial
    obtain ⟨P, z, hz⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨P, ?_⟩
    have he : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rwa [he] at hz

/-- The actual full kernel's scheme points are exactly the original subgroup. -/
def veluGlobalKernelPointEquiv : G ≃ veluGlobalKernel E G hodd :=
  Equiv.ofBijective (fun P ↦ veluGlobalKernelPoint E G hodd P (IsLocalRing.closedPoint K))
    (veluGlobalKernelPoint_bijective E G hodd)

/-- Cardinality of the actual fiber, with no reduction or alternate kernel. -/
theorem veluGlobalKernel_card : Nat.card (veluGlobalKernel E G hodd) = Nat.card G :=
  (Nat.card_congr (veluGlobalKernelPointEquiv E G hodd)).symm

/-- The full scheme-theoretic identity fiber has length equal to the original subgroup order. -/
theorem veluGlobalKernel_length :
    FLT.Mazur.FCurve.finiteSchemeLength
      (pullback.snd (veluGlobalMorphism E G hodd) (integralCurveZero (curve E G))) =
        Nat.card G := by
  rw [veluGlobalKernel_length_eq_card, veluGlobalKernel_card]

/-- Its finite flat rank is the original subgroup order at every point of the field spectrum. -/
theorem veluGlobalKernel_rank (s : Spec (.of K)) :
    (pullback.snd (veluGlobalMorphism E G hodd) (integralCurveZero (curve E G))).finrank s =
      Nat.card G := by
  rw [FLT.Mazur.FCurve.finiteUnramifiedField_rank_eq_card, veluGlobalKernel_card]

end WeierstrassCurve.Velu

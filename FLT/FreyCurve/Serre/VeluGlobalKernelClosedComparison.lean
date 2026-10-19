/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalKernelEtale
public import FLT.Mazur.WeierstrassOriginIdealSheaf

/-!
# Identifying an original closed subgroup with the full Vélu fiber

A closed subscheme killed by the original map and containing each original
subgroup section maps isomorphically to the full reduced kernel.
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
  {H : Scheme} (i : H ⟶ integralCurve E) (s : H ⟶ Spec (.of K))
  (hz : i ≫ veluGlobalMorphism E G hodd = s ≫ integralCurveZero (curve E G))

/-- The canonical comparison induced by the original inclusion and zero-image equation. -/
def veluGlobalKernelClosedLift : H ⟶ veluGlobalKernel E G hodd :=
  pullback.lift i s hz

/-- The comparison retains the original closed inclusion. -/
@[reassoc] theorem veluGlobalKernelClosedLift_fst :
    veluGlobalKernelClosedLift E G hodd i s hz ≫ pullback.fst _ _ = i :=
  pullback.lift_fst _ _ _

/-- The comparison retains the original coefficient map. -/
@[reassoc] theorem veluGlobalKernelClosedLift_snd :
    veluGlobalKernelClosedLift E G hodd i s hz ≫ pullback.snd _ _ = s :=
  pullback.lift_snd _ _ _

/-- A closed original inclusion gives a closed comparison with the actual fiber. -/
instance veluGlobalKernelClosedLift_closed [IsClosedImmersion i] :
    IsClosedImmersion (veluGlobalKernelClosedLift E G hodd i s hz) := by
  let _ : IsClosedImmersion
      (veluGlobalKernelClosedLift E G hodd i s hz ≫ pullback.fst _ _) := by
    rw [veluGlobalKernelClosedLift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (pullback.fst _ _)

/-- Every retained original section maps to its identical section in the full fiber. -/
@[reassoc] theorem veluGlobalKernelClosedLift_section (P : G) (e : Spec (.of K) ⟶ H)
    (hi : e ≫ i = affineSmoothPoint E P.val ≫ (integralSmoothOpen E).ι)
    (hs : e ≫ s = 𝟙 _) :
    e ≫ veluGlobalKernelClosedLift E G hodd i s hz = veluGlobalKernelPoint E G hodd P := by
  apply pullback.hom_ext
  · rw [Category.assoc, veluGlobalKernelClosedLift_fst, hi, veluGlobalKernelPoint_fst]
  · rw [Category.assoc, veluGlobalKernelClosedLift_snd, hs, veluGlobalKernelPoint_snd]

include hz in
/-- Original section coverage proves the closed comparison is an isomorphism of schemes. -/
theorem veluGlobalKernelClosedLift_isIso [IsClosedImmersion i]
    (hc : ∀ P : G, ∃ e : Spec (.of K) ⟶ H,
      e ≫ i = affineSmoothPoint E P.val ≫ (integralSmoothOpen E).ι ∧ e ≫ s = 𝟙 _) :
    IsIso (veluGlobalKernelClosedLift E G hodd i s hz) := by
  let _ : Surjective (veluGlobalKernelClosedLift E G hodd i s hz) := by
    constructor
    intro x
    have hx : x ∈ ⨆ P : G, (veluGlobalKernelPoint E G hodd P).opensRange := by
      rw [veluGlobalKernelPoint_iSup_eq_top]
      trivial
    obtain ⟨P, z, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨e, hi, hs⟩ := hc P
    refine ⟨e z, ?_⟩
    exact congrArg (fun f : Spec (.of K) ⟶ veluGlobalKernel E G hodd ↦ f z)
      (veluGlobalKernelClosedLift_section E G hodd i s hz P e hi hs)
  exact isIso_of_isClosedImmersion_of_surjective _

end WeierstrassCurve.Velu

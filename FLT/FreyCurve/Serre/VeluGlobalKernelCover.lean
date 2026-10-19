/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalKernelPointsOpen

/-!
# The original subgroup sections cover the full scheme-theoretic kernel

The finite kernel is Jacobson. Every field section comes from the original
subgroup, so their open images cover all its scheme points.
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

/-- Every field section of the actual fiber is one of the original subgroup sections. -/
theorem veluGlobalKernelPoint_surjective
    (p : Spec (.of K) ⟶ veluGlobalKernel E G hodd)
    (hp : p ≫ pullback.snd _ _ = 𝟙 (Spec (.of K))) :
    ∃ P : G, veluGlobalKernelPoint E G hodd P = p := by
  have hz : (p ≫ pullback.fst _ _) ≫ veluGlobalMorphism E G hodd =
      integralCurveZero (curve E G) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, Category.id_comp]
  have hb : (p ≫ pullback.fst _ _) ≫ integralCurveStructure E = 𝟙 _ := by
    rw [← veluGlobalMorphism_base E G hodd, ← Category.assoc, hz]
    exact integralCurveZero_structure (curve E G)
  obtain ⟨P, hP⟩ := veluGlobalMorphism_section_kernel E G hodd _ hb hz
  refine ⟨P, pullback.hom_ext ?_ ?_⟩
  · rw [veluGlobalKernelPoint_fst, hP]
  · rw [veluGlobalKernelPoint_snd, hp]

/-- The open images of the original subgroup sections cover the entire finite fiber. -/
theorem veluGlobalKernelPoint_iSup_eq_top :
    ⨆ P : G, (veluGlobalKernelPoint E G hodd P).opensRange = ⊤ := by
  apply FLT.Mazur.AlgClosedOpenCover.eq_top_of_sections (pullback.snd _ _)
  intro p hp
  obtain ⟨P, rfl⟩ := veluGlobalKernelPoint_surjective E G hodd p hp
  rintro _ ⟨z, rfl⟩
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨P, ?_⟩
  exact ⟨z, rfl⟩

/-- A scheme open cover of the actual kernel by its original subgroup points. -/
def veluGlobalKernelOpenCover : (veluGlobalKernel E G hodd).OpenCover where
  I₀ := G
  X _ := Spec (.of K)
  f := veluGlobalKernelPoint E G hodd
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : x ∈ ⨆ P : G, (veluGlobalKernelPoint E G hodd P).opensRange := by
      rw [veluGlobalKernelPoint_iSup_eq_top]
      trivial
    obtain ⟨P, hP⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨P, hP⟩

end WeierstrassCurve.Velu

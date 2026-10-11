/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCommonModelFiltration
public import FLT.Mazur.LocalCompletionModelModule

/-!
# Filtrations on modules transported to an arithmetic local model

Equality of the extended original ideals transports the actual local
filtration to the other original ring, including its separatedness.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalCompletionModelFiltration

variable {R A B C N : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R C] [Algebra B C] [IsLocalRing A]
  (e : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[R] C)
  [AddCommGroup N] [Module (AdicCompletion (IsLocalRing.maximalIdeal A) A) N]
  [Module A N] [IsScalarTower A (AdicCompletion (IsLocalRing.maximalIdeal A) A) N]
  (J : Ideal B)
  (h : (IsLocalRing.maximalIdeal A).map (LocalCompletionModel.scalars e) =
    J.map (algebraMap B C))

include h

/-- The transported module filtration is exactly the original local filtration. -/
theorem mem_power_iff (m : ℕ) (x : N) :
    let _ := LocalCompletionModelModule.modelModule (N := N) e
    let _ := Module.compHom N (algebraMap B C)
    x ∈ IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A N) ↔
      x ∈ J ^ m • (⊤ : Submodule B N) := by
  let _ := (LocalCompletionModel.scalars e).toAlgebra
  let _ := LocalCompletionModelModule.modelModule (N := N) e
  let _ := LocalCompletionModelModule.scalarTower (N := N) e
  let _ := Module.compHom N (algebraMap B C)
  let _ : IsScalarTower B C N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact AdicCommonModelFiltration.mem_power_iff _ J h m x

/-- The transported arithmetic ideal separates every originally separated local module. -/
theorem isHausdorff [IsHausdorff (IsLocalRing.maximalIdeal A) N] :
    let _ := LocalCompletionModelModule.modelModule (N := N) e
    let _ := Module.compHom N (algebraMap B C)
    IsHausdorff J N := by
  let _ := (LocalCompletionModel.scalars e).toAlgebra
  let _ := LocalCompletionModelModule.modelModule (N := N) e
  let _ := LocalCompletionModelModule.scalarTower (N := N) e
  let _ := Module.compHom N (algebraMap B C)
  let _ : IsScalarTower B C N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact (AdicCommonModelFiltration.isHausdorff_iff _ J h).mp inferInstance

end FLT.Mazur.LocalCompletionModelFiltration

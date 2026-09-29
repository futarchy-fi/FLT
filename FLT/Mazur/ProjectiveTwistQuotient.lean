/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import FLT.Mazur.ProjectiveGeneration
public import FLT.Mazur.ProjectiveChartNoetherian

/-! # Coherent presentations by finite sums of negative twists -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Twisting is an equivalence, with opposite twist as inverse. -/
def twistTensorEquivalence (d : ℤ) : (space R ι).Modules ≌ (space R ι).Modules :=
  CategoryTheory.Equivalence.mk (twistTensorFunctor R ι d) (twistTensorFunctor R ι (-d))
    (twistTensorNegNatIso R ι d).symm (twistTensorNegNatIso' R ι d)

instance twistTensorFunctor_preservesEpimorphisms (d : ℤ) :
    (twistTensorFunctor R ι d).PreservesEpimorphisms :=
  inferInstanceAs (twistTensorEquivalence R ι d).functor.PreservesEpimorphisms

variable [Finite ι]

/-- Untwisting global generators gives a finite sum of negative twists onto the sheaf. -/
theorem exists_twist_sum_epi (F : (space R ι).Modules) [F.IsFinitePresentation] :
    ∃ (d : ℕ) (κ : Type u) (_ : Finite κ)
      (p : (∐ fun _ : κ ↦ twistingSheaf R ι (-(d : ℤ))) ⟶ F), Epi p := by
  obtain ⟨d, κ, hκ, p, hp⟩ := exists_twist_finite_free_epi R ι F
  let _finite := hκ
  let _epi := hp
  refine ⟨d, κ, hκ, (twistTensorFreeIso R ι (-(d : ℤ)) κ).inv ≫
    (twistTensorFunctor R ι (-(d : ℤ))).map p ≫
      (twistTensorNegIso R ι F (d : ℤ)).hom, ?_⟩
  infer_instance

/-- The finite twist presentation has a coherent kernel over a Noetherian base. -/
theorem exists_coherent_twist_presentation [IsNoetherianRing R]
    (F : (space R ι).Modules) [F.IsFinitePresentation] :
    ∃ (d : ℕ) (κ : Type u) (_ : Finite κ)
      (p : (∐ fun _ : κ ↦ twistingSheaf R ι (-(d : ℤ))) ⟶ F),
      FCurve.CoherentDevissage.CoherentSequence (ShortComplex.kernelSequence p) := by
  obtain ⟨d, κ, hκ, p, hp⟩ := exists_twist_sum_epi R ι F
  let _finite := hκ
  let _epi := hp
  have _freeCoherent :
      (SheafOfModules.free (R := (space R ι).ringCatSheaf) κ).IsFinitePresentation := by
    let q := (SheafOfModules.free.generatingSections
      (R := (space R ι).ringCatSheaf) κ).localGeneratorsData.quasiCoherentData
    refine { exists_quasicoherentData := ⟨q, ?_⟩ }
    refine { isFinite_presentation := fun i ↦ ?_ }
    exact { isFiniteType_generators := ⟨inferInstanceAs (Finite κ)⟩
            isFiniteType_relations := ⟨inferInstanceAs (Finite (ULift Empty))⟩ }
  have _sourceCoherent :
      (∐ fun _ : κ ↦ twistingSheaf R ι (-(d : ℤ))).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (space R ι).ringCatSheaf).prop_of_iso
      (twistTensorFreeIso R ι (-(d : ℤ)) κ)
      (show (twistTensor R ι (SheafOfModules.free κ) (-(d : ℤ))).IsFinitePresentation
        from inferInstance)
  exact ⟨d, κ, hκ, p, FCurve.CoherentDevissage.coherent_kernelSequence p⟩

end FLT.Mazur.ProjectiveSpace

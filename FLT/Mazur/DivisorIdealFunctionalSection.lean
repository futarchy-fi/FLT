/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection
public import FLT.Mazur.DivisorLineBundlePower
public import FLT.Mazur.IdealComplementFunctionExtension

/-!
# Actual divisor sections from cleared ideal denominators

A functional on an ideal power gives a global section of its dual divisor
line. On the complement its restriction is the prescribed multiplication
by the original function. The same section has an actual tensor-power
numerator via the existing divisor-power comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
open GlobalIdealPowerCompatibility ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Dualize an actual ideal functional into a section on any open. -/
def divisorFunctionalSection (f : idealModule I ⟶ structureModule X) (U : X.Opens) :
    Γ(divisorLineBundle I hI, U) :=
  (moduleSheafDualUnitIso.inv ≫ moduleSheafDualMap (idealModule I) f).app U (1 : Γ(X, U))

/-- This section is the original functional restricted to the indicated open. -/
theorem divisorFunctionalSection_eq (f : idealModule I ⟶ structureModule X) (U : X.Opens) :
    divisorFunctionalSection hI f U =
      (restrictFunctor U.ι).map f ≫ moduleDualUnitSection U 1 := rfl

/-- The functional sections agree under every open restriction. -/
theorem divisorFunctionalSection_restrict (f : idealModule I ⟶ structureModule X)
    {U V : X.Opens} (h : V ≤ U) :
    (divisorLineBundle I hI).presheaf.map (homOfLE h).op (divisorFunctionalSection hI f U) =
      divisorFunctionalSection hI f V := by
  let F := moduleSheafDualUnitIso.inv ≫ moduleSheafDualMap (idealModule I) f
  have hn := congrArg (fun k ↦ k (1 : Γ(X, U)))
    (F.mapPresheaf.naturality (homOfLE h).op)
  change F.app V (X.presheaf.map (homOfLE h).op 1) =
    (divisorLineBundle I hI).presheaf.map (homOfLE h).op
      (divisorFunctionalSection hI f U) at hn
  simpa only [map_one, F, divisorFunctionalSection] using hn.symm

/-- Complement functions extend to global sections of an actual divisor power. -/
theorem exists_divisorFunctionalSection [IsNoetherian X]
    (a : Γ((complement I).toScheme, ⊤)) :
    ∃ m : ℕ, ∃ t : Γ(divisorLineBundle (I ^ m) (hI.pow m), ⊤),
      (divisorLineBundle (I ^ m) (hI.pow m)).presheaf.map
        (complement I).leTop.op t =
      (restrictFunctor (complement I).ι).map (idealModuleι (I ^ m)) ≫
        IdealPowerScalarLift.scalarEnd ((structureModule X).restrict (complement I).ι) a ≫
          moduleDualUnitSection (complement I) 1 := by
  obtain ⟨m, f, hf⟩ := IdealComplementFunctionExtension.exists_function_denominator I a
  refine ⟨m, divisorFunctionalSection (hI.pow m) f ⊤, ?_⟩
  exact (divisorFunctionalSection_restrict (hI.pow m) f le_top).trans
    ((divisorFunctionalSection_eq (hI.pow m) f _).trans (by rw [hf, Category.assoc]))

/-- The extended function also has a numerator in the original tensor powers of O(D). -/
theorem exists_divisorTensorNumerator [IsNoetherian X]
    (a : Γ((complement I).toScheme, ⊤)) :
    ∃ m : ℕ, ∃ t : Γ(tensorPower (divisorLineBundle I hI) m, ⊤),
      (divisorLineBundle (I ^ m) (hI.pow m)).presheaf.map (complement I).leTop.op
        ((divisorLineBundlePowerIso hI m).hom.app ⊤ t) =
      (restrictFunctor (complement I).ι).map (idealModuleι (I ^ m)) ≫
        IdealPowerScalarLift.scalarEnd ((structureModule X).restrict (complement I).ι) a ≫
          moduleDualUnitSection (complement I) 1 := by
  obtain ⟨m, t, ht⟩ := exists_divisorFunctionalSection hI a
  refine ⟨m, (divisorLineBundlePowerIso hI m).inv.app ⊤ t, ?_⟩
  convert ht using 1
  exact congrArg ((divisorLineBundle (I ^ m) (hI.pow m)).presheaf.map
    (complement I).leTop.op)
    (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app ⊤)
      (divisorLineBundlePowerIso hI m).inv_hom_id) t)

end FLT.Mazur.FCurve

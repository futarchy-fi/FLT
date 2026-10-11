/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementLinear
public import FLT.Mazur.DivisorTensorNumeratorComparison

/-!
# Exhaustion of complement functions by original divisor poles

On a Noetherian scheme, every regular function off an effective Cartier
divisor is the coordinate of an actual global tensor-power section of O(D).
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open GlobalIdealPowerCompatibility ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} [IsNoetherian X] {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Every complement function is represented by an original global tensor numerator. -/
theorem exists_divisorComplementFunction (a : Γ((complement I).toScheme, ⊤)) :
    ∃ m : ℕ, ∃ t : Γ(tensorPower (divisorLineBundle I hI) m, ⊤),
      divisorComplementFunction hI m t = a := by
  obtain ⟨m, t, ht⟩ := exists_divisorTensorNumerator hI a
  exact ⟨m, t, divisorComplementFunction_of_numerator hI m t a ht⟩

/-- Every actual regular complement function has a finite original pole bound. -/
theorem exists_mem_divisorPoleFunctions (a : Γ((complement I).toScheme, ⊤)) :
    ∃ m, a ∈ divisorPoleFunctions hI m := by
  obtain ⟨m, t, ht⟩ := exists_divisorComplementFunction hI a
  exact ⟨m, (mem_divisorPoleFunctions hI m a).mpr ⟨t, ht⟩⟩

variable {k : Type} [Field k] (f : X ⟶ Spec (.of k))

/-- Every complement function lies in a bounded pole subspace for the actual field action. -/
theorem exists_mem_divisorPoleSubmodule (a : divisorComplementModule f I) :
    ∃ m, a ∈ divisorPoleSubmodule f hI m := by
  obtain ⟨m, hm⟩ := exists_mem_divisorPoleFunctions hI a
  exact ⟨m, (mem_divisorPoleSubmodule f hI m a).mpr hm⟩

/-- The original bounded pole subspaces exhaust the actual complement function module. -/
theorem iSup_divisorPoleSubmodule_eq_top :
    (⨆ m, divisorPoleSubmodule f hI m) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨m, hm⟩ := exists_mem_divisorPoleSubmodule hI f a
  exact (le_iSup (divisorPoleSubmodule f hI) m) hm

end FLT.Mazur.FCurve

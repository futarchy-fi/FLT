/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReesRelativeNaturality
public import FLT.Mazur.ReesModuleBaseChange
public import FLT.Mazur.ReesModuleMap

/-!
# Semilinear maps of the actual relative Rees modules

The actual extended-power modules restrict over the tensor-product ring
maps. Their coefficients are the original semilinear maps, and scalar
compatibility follows from naturality of the relative Rees quotient.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.Rees

variable {R S T M N : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [AddCommGroup M] [AddCommGroup N]
  [Module S M] [Module T N] (I : Ideal R) (f : S →ₐ[R] T) (g : M →ₛₗ[f.toRingHom] N)

/-- A semilinear coefficient map preserves the extended ideal-power multiples. -/
lemma extendedModuleMap_mem (n : ℕ) (m : M)
    (hm : m ∈ (I.map (Algebra.algebraMap R S)) ^ n • (⊤ : Submodule S M)) :
    g m ∈ (I.map (Algebra.algebraMap R T)) ^ n • (⊤ : Submodule T N) := by
  refine Submodule.smul_induction_on hm (fun r hr m _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem_smul
      (map_pow_le _ _ _ (extendedIdeal_map I f).le n (Ideal.mem_map_of_mem _ hr))
      (by trivial)
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- The coefficient map on the actual extended-ideal Rees modules. -/
def extendedModuleMap : extendedModule (S := S) (M := M) I →ₛₗ[extendedAlgebraMap I f]
    extendedModule (S := T) (M := N) I :=
  moduleMap g _ _ (extendedIdeal_map I f).le _ _ (extendedModuleMap_mem I f g)

/-- The same original coefficient map is semilinear over the relative tensor rings. -/
def relativeModuleMap :
    let _ := relativeModule (S := S) (M := M) I
    let _ := relativeModule (S := T) (M := N) I
    extendedModule (S := S) (M := M) I →ₛₗ[(relativeAlgebraMap I f).toRingHom]
      extendedModule (S := T) (M := N) I := by
  let _ := relativeModule (S := S) (M := M) I
  let _ := relativeModule (S := T) (M := N) I
  refine
    { toFun := extendedModuleMap I f g
      map_add' := map_add _
      map_smul' := ?_ }
  intro r m
  change extendedModuleMap I f g (relativeMap I r • m) =
    relativeMap I (relativeAlgebraMap I f r) • extendedModuleMap I f g m
  rw [map_smulₛₗ, relativeMap_naturality]

/-- Relative maps retain the actual section restriction on every coefficient. -/
lemma relativeModuleMap_coeff (s : extendedModule (S := S) (M := M) I) (n : ℕ) :
    (relativeModuleMap I f g s).val.coeff n = g (s.val.coeff n) := rfl

/-- Injective coefficient maps give injective relative Rees module maps. -/
lemma relativeModuleMap_injective (hg : Function.Injective g) :
    Function.Injective (relativeModuleMap I f g) :=
  moduleMap_injective g _ _ (extendedIdeal_map I f).le _ _
    (extendedModuleMap_mem I f g) hg

end FLT.Mazur.Rees

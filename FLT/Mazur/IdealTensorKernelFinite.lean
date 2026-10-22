/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatIdealTensor
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Finite ideal-tensor obstruction modules

Over a Noetherian target algebra the kernel testing a finitely generated
base ideal is finite over the target. The algebra need not be module finite
over the base. Its generators admit actual finite pure-tensor expressions.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorKernel
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The obstruction to injectivity for the actual extended ideal. -/
def obstruction (I : Ideal R) : Submodule S (S ⊗[R] I) :=
  LinearMap.ker (FCurve.idealTensorInclusion I)

/-- No finiteness over the base is imposed on the target algebra. -/
theorem obstruction_finite [IsNoetherianRing S] (I : Ideal R) (hI : I.FG) :
    Module.Finite S (obstruction (S := S) I) := by
  let _ : Module.Finite R I := Module.Finite.of_fg hI
  infer_instance

/-- Finite generators of the whole obstruction, in the ambient tensor module. -/
theorem exists_generators [IsNoetherianRing S] (I : Ideal R) (hI : I.FG) :
    ∃ (n : ℕ) (z : Fin n → S ⊗[R] I),
      Submodule.span S (Set.range z) = obstruction I := by
  let _ := obstruction_finite (S := S) I hI
  exact Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.Finite.iff_fg.mp inferInstance)

/-- Every obstruction element is an explicit finite relation in the ideal. -/
theorem exists_relation (I : Ideal R) (z : obstruction (S := S) I) :
    ∃ (n : ℕ) (x : Fin n → S) (a : Fin n → I),
      (∑ k, x k ⊗ₜ[R] a k) = z.val ∧
      ∑ k, x k * algebraMap R S (a k) = 0 := by
  obtain ⟨n, x, a, h⟩ := TensorProduct.exists_sum_tmul_eq z.val
  refine ⟨n, x, a, h.symm, ?_⟩
  have hz := z.property
  change FCurve.idealTensorInclusion I z.val = 0 at hz
  simpa only [h, map_sum, FCurve.idealTensorInclusion_tmul] using hz

end FLT.Mazur.IdealTensorKernel

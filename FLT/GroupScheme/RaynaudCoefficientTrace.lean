/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudHigherWeightTrace
public import FLT.GroupScheme.RaynaudModelTameSpectrum

/-!
# Nonzero trace over the original coefficient field

Construct an actual simple prime-field quotient of the finite-flat points.
Only Cayley–Hamilton on the original k-linear operator uses dimension two.
No scalar model, weight, quotient, spectrum or generator is an input.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "I" => localInertiaGroup v

variable {k : Type} [Field k] [CharP k p]
  (M : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) [Module k M.Points]
  (ρ : Representation k (localInertiaGroup (LocalCyclotomic.rationalPlace p)) M.Points)

set_option maxHeartbeats 1600000 in
-- The actual quotient retains the original points and their canonical inertia action.
/-- Flatness and cyclotomic determinant force nonzero original coefficient-field trace. -/
theorem coefficient_flat_trace_ne_zero (hp : 3 < p)
    (hact : ∀ σ x, ρ σ x = σ • x)
    (hdim : Module.finrank k M.Points = 2)
    (hdet : ∀ σ : I, (ρ σ).det = ZMod.castHom (dvd_refl p) k
      ((LocalRoot.modCyclotomic p σ.1 : (ZMod p)ˣ) : ZMod p)) :
    ∃ σ : I, orderOf (LocalRoot.modCyclotomic p σ.1) = p - 1 ∧
      LinearMap.trace k M.Points (ρ σ) ≠ 0 := by
  let : Module (ZMod p) M.Points := Module.compHom M.Points (ZMod.castHom (dvd_refl p) k)
  let : Nontrivial M.Points := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank k M.Points)
  let ρ₀ := M.primeInertiaRepresentation p
  obtain ⟨N, hN⟩ := ρ₀.exists_coatom_subrepresentation
  let W := M.Points ⧸ N.toSubmodule
  let ρW := ρ₀.quotient N.toSubmodule N.apply_mem_toSubmodule
  let : ρW.IsIrreducible := ρ₀.quotient_irreducible_of_isCoatom N hN
  let : Finite W := Finite.of_surjective N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective
  let : DistribMulAction I W := DistribMulAction.compHom _ ρW
  let : TopologicalSpace (Module.End (ZMod p) W)ˣ := ⊥
  let : DiscreteTopology (Module.End (ZMod p) W)ˣ := ⟨rfl⟩
  let q : M.Points →+[I] W :=
    { toAddMonoidHom := N.toSubmodule.mkQ.toAddMonoidHom
      map_smul' := fun _ _ ↦ rfl }
  have hc : Continuous ρW.toHomUnits := ρW.continuous_toHomUnits_iff_discrete.mpr
    ((M.primeInertiaRepresentation_continuous p).quotient ρ₀ N)
  exact higher_quotient_trace_ne_zero p M ρ ρW hp hact hc (fun _ _ ↦ rfl)
    q N.toSubmodule.mkQ_surjective hdim hdet

end ThreeAdicPlan

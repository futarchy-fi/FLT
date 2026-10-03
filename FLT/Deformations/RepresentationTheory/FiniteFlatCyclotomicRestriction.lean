/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.FiniteFlatCyclotomicTrace
public import FLT.Deformations.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Cyclotomic restriction after extending the original coefficients

Extend the trace of the original finite-flat representation, not its finite
point model. The same original inertia element detects the quadratic self-twist.
This large-prime result has no p = 2 or p = 3 branch.
-/

@[expose] public noncomputable section
namespace GaloisRep
open NumberField
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "j" => Field.absoluteGaloisGroup.map (algebraMap ℚ Kv)

/-- Finite flatness preserves kernel irreducibility over algebraically closed extensions. -/
theorem flat_cyclotomic_restriction_baseChange {k V : Type} [Field k] [TopologicalSpace k]
    [CharP k p] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : GaloisRep ℚ k V) (hp : 3 < p)
    (hflat : ρ.HasFlatProlongationAt v) (hdim : Module.finrank k V = 2)
    (hdet : ∀ g, (ρ g).det = ZMod.castHom (dvd_refl p) k (CyclotomicQuadratic.character p g))
    (E : Type*) [Field E] [Algebra k E] [IsAlgClosed E]
    (hirr : (Representation.baseChange E ρ.toRepresentation).IsIrreducible) :
    Representation.IsIrreducible ((Representation.baseChange E ρ.toRepresentation).comp
      (CyclotomicQuadratic.character p).ker.subtype) := by
  let : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
  obtain ⟨σ, hσ, ht⟩ := ρ.flat_cyclotomic_generator_trace p hp hflat hdim hdet
  have htwo : (2 : E) ≠ 0 := fun h ↦
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega) ((CharP.cast_eq_zero_iff E p 2).mp h)
  apply CyclotomicQuadratic.irreducible_restriction_of_inertia_trace p
    (Representation.baseChange E ρ.toRepresentation)
    (by simpa only [Module.finrank_baseChange] using hdim) htwo hirr σ hσ
  change LinearMap.trace E (E ⊗[k] V) ((ρ (j σ.1)).baseChange E) ≠ 0
  rw [LinearMap.trace_baseChange]
  exact (_root_.map_ne_zero _).mpr ht

end GaloisRep

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudPrimeTameSpectrum
public import FLT.GroupScheme.RaynaudAgreedPointAction

/-!
# Tame spectrum of the original model action

The prime-field representation and its continuity come from the original
finite-flat points. Only rank and the actual determinant are additional inputs.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing Polynomial

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "k" => ResidueField (IntegralClosure O (AlgebraicClosure Kv))
attribute [local instance] LocalRoot.rationalResidue_charP

/-- The original model's prime-field action restricted to original local inertia. -/
def FF.primeInertiaRepresentation (M : FF O Kv) [Module (ZMod p) M.Points] :
    Representation (ZMod p) (localInertiaGroup v) M.Points :=
  (M.primeRepresentation p).comp (localInertiaGroup v).subtype

/-- The original model's inertia representation has open evaluation fibres. -/
theorem FF.primeInertiaRepresentation_continuous (M : FF O Kv) [Module (ZMod p) M.Points] :
    (M.primeInertiaRepresentation p).IsDiscreteContinuous := by
  intro x y
  exact (ContinuousSMulDiscrete.isOpen_smul_eq (Field.absoluteGaloisGroup Kv) x y).preimage
    continuous_subtype_val

/-- The actual model action has the derived spectrum at a cyclotomic generator. -/
theorem FF.primeInertia_tame_spectrum (hp : 3 < p)
    (M : FF O Kv) [Module (ZMod p) M.Points]
    (hdim : Module.finrank (ZMod p) M.Points = 2)
    (hdet : ∀ σ : localInertiaGroup v,
      (M.primeInertiaRepresentation p σ).det =
        ((LocalRoot.modCyclotomic p σ.1 : (ZMod p)ˣ) : ZMod p)) :
    ∃ σ : localInertiaGroup v,
      orderOf (LocalRoot.modCyclotomic p σ.1) = p - 1 ∧
      ∃ a b : kˣ,
        (M.primeInertiaRepresentation p σ).charpoly.map (ZMod.castHom (dvd_refl p) k) =
          (X - C (a : k)) * (X - C (b : k)) ∧
        (orderOf (a / b) = p - 1 ∨ orderOf (a / b) = p + 1) ∧
        LinearMap.trace (ZMod p) M.Points (M.primeInertiaRepresentation p σ) ≠ 0 :=
  prime_flat_tame_spectrum p hp M (M.primeInertiaRepresentation p)
    (M.primeInertiaRepresentation_continuous p) (fun _ _ ↦ rfl) hdim hdet

end ThreeAdicPlan

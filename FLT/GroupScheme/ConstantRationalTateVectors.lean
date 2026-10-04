/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantRationalPowerSystem
public import FLT.GroupScheme.ConstantPowerCharacters
public import FLT.GroupScheme.RationalCyclotomicRoots

/-! # Actual constant and cyclotomic Tate vectors at the original rational place -/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ConstantRationalPower
open ConstantPower
variable (p : ℕ) [Fact p.Prime] (hp : 2 < p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- The compatible residue classes of one form an actual Tate vector. -/
def generator : (system p hp).tateSequences :=
  ⟨fun n ↦ points p n (Ideal.Quotient.mk _ 1), fun h ↦ by
    change genericHom (reduction p h) _ = _
    rw [reduction_points, reduce_mk]⟩

/-- The chosen cyclotomic root defines a character of each actual constant point group. -/
def cyclotomicCharacter (n : ℕ) :
    Multiplicative (level p n).Points →* (AlgebraicClosure K)ˣ :=
  ((rootCharacter p n (rationalCyclotomicUnit p n) (rationalCyclotomicUnit_pow p n)).comp
    (points p n).symm.toAddMonoidHom).toMultiplicativeLeft

/-- Character evaluation on residues is the chosen root character. -/
theorem cyclotomicCharacter_points (n : ℕ) (a : Residue p n) :
    cyclotomicCharacter p n (Multiplicative.ofAdd (points p n a)) =
      (rootCharacter p n (rationalCyclotomicUnit p n)
        (rationalCyclotomicUnit_pow p n) a).toMul := by
  change (rootCharacter p n (rationalCyclotomicUnit p n) (rationalCyclotomicUnit_pow p n)
    ((points p n).symm (points p n a))).toMul = _
  rw [AddEquiv.symm_apply_apply]

/-- Perfect finite Cartier duality realizes that character as an actual dual point. -/
def cyclotomicDualPoint (n : ℕ) : (level p n).cartierDual.Points :=
  (level p n).cartierCharactersEquiv.symm (Additive.ofMul (cyclotomicCharacter p n))

/-- The finite pairing is exactly the specified root character. -/
theorem cyclotomicDualPoint_pairing (n : ℕ) (a : Residue p n) :
    (level p n).cartierPairing (cyclotomicDualPoint p n) (points p n a) =
      (rootCharacter p n (rationalCyclotomicUnit p n)
        (rationalCyclotomicUnit_pow p n) a).toMul := by
  rw [← FF.cartierCharactersEquiv_apply, cyclotomicDualPoint, AddEquiv.apply_symm_apply]
  exact cyclotomicCharacter_points p n a

/-- Original transposed inclusions give the actual cyclotomic transition law. -/
theorem cyclotomicDualPoint_transition {m n : ℕ} (h : m ≤ n) :
    genericHom (inclusion p h).cartierDual (cyclotomicDualPoint p n) =
      cyclotomicDualPoint p m := by
  apply (level p m).cartierPairing_separates_dual
  intro x
  obtain ⟨a, rfl⟩ := (points p m).surjective x
  rw [ModelHom.cartierPairing_naturality, inclusion_points, cyclotomicDualPoint_pairing,
    cyclotomicDualPoint_pairing, rootCharacter_embed p h _ _ _ _
      (rationalCyclotomicUnit_transition p h)]

/-- The chosen roots give a coherent point of the genuine Cartier-dual Tate module. -/
def cyclotomicVector : (system p hp).CartierTate :=
  ⟨cyclotomicDualPoint p, fun h ↦ cyclotomicDualPoint_transition p h⟩

/-- Pairing these two actual Tate vectors gives the fixed original cyclotomic unit. -/
theorem tatePairing_generator (n : ℕ) :
    (system p hp).cartierTatePairing (cyclotomicVector p hp) (generator p hp) n =
      rationalCyclotomicUnit p n := by
  change (level p n).cartierPairing (cyclotomicDualPoint p n)
    (points p n (Ideal.Quotient.mk _ 1)) = _
  rw [cyclotomicDualPoint_pairing, rootCharacter_mk, zpow_one]
  rfl

end ThreeAdicPlan.ConstantRationalPower

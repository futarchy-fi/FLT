/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PeuPrimeUnitSubspace
public import FLT.LocalClassFieldTheory.PeuExtendedSpan
public import FLT.LocalClassFieldTheory.LinearCoefficientEquivalence
public import FLT.GaloisRepresentation.Extensions.ExtendedUnitSubspace

/-!
# The independent unit annihilator over an extended residual field

The existing extended unit subspace equals the existing cup-annihilator.
The proof transports both dual characters and continuous boundaries through
finite coefficient coordinates, then invokes the prime arithmetic theorem.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing KummerTheory GaloisRepresentation.Extensions

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (K C : Type) [Field K] [Field C] [IsAlgClosed C] [Algebra K C]
  [Algebra.IsSeparable K C] [CharZero C] (A : ValuationSubring K)
  [IsDiscreteValuationRing A] [Finite (ResidueField A)]
  [IsAdicComplete (maximalIdeal A) A] {q : ℕ} [Fact q.Prime]
  {ζ : Cˣ} (hζ : IsPrimitiveRoot ζ q)
  (k : Type*) [Field k] [TopologicalSpace k] [DiscreteTopology k] [Algebra (ZMod q) k]
  [FiniteDimensional (ZMod q) k]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]

local notation "χ" => primeCyclotomicCharacter (K := K) hζ
local notation "I" => MonoidHom.ker (unramifiedRestriction A K C)
local notation "roots" => exists_unit_root (K := K) (L := C) (n := q)

include p in
/-- The full residual-field annihilator equals the independently defined extended unit subspace. -/
theorem peuClassSubmodule_eq_extendedUnitSubspace :
    peuClassSubmodule (F := k) (M := CharacterModule χ k) I =
      extendedUnitSubspace hζ k roots A := by
  classical
  let b := Module.finBasis (ZMod q) k
  rw [peuClassSubmodule_eq_extendedSpan χ b I]
  unfold extendedUnitSubspace
  congr 1
  let e := primeCyclotomicLinearCoordinates (K := K) hζ
  have he : ∀ (g : Gal(C/K)) (x : CharacterModule χ (ZMod q)),
      e (g • x) = g • e x := primeCyclotomicCoordinates_equivariant hζ
  let E := linearCoefficientClassEquiv e he
  have hE (x : LinearContinuousClass (ZMod q) Gal(C/K) (CharacterModule χ (ZMod q))) :
      E x ∈ primeUnitSubspace roots A ↔ x ∈ peuClassSubmodule I :=
    (isPeuRamifiedClass_iff_primeUnitSubspace K C A q p (E x)).symm.trans
      (linearCoefficientClassEquiv_peu e he I x)
  have hcomp (x : LinearContinuousClass (ZMod q) Gal(C/K)
      (CharacterModule χ (ZMod q))) :
      extendRootClass hζ k (E x) = extendCharacterClass (k := k) χ x := by
    induction x using Quotient.inductionOn with | h c =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      apply Subtype.ext
      apply ContinuousMap.ext
      intro g
      change algebraMap (ZMod q) k (e.symm (e (c.1 g))) = algebraMap (ZMod q) k (c.1 g)
      rw [e.symm_apply_apply]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨E y, (hE y).mpr hy, hcomp y⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := E.surjective y
    exact ⟨z, (hE z).mp hy, (hcomp z).symm⟩

include p in
/-- The independent predicate on the original quotient is exactly the extended unit criterion. -/
theorem isPeuRamifiedClass_iff_extendedUnitClass
    (x : ContinuousClass Gal(C/K) (CharacterModule χ k)) :
    IsPeuRamifiedClass (k := k) I x ↔ IsExtendedUnitClass hζ k roots A x := by
  obtain ⟨y, rfl⟩ := (linearClassEquiv (k := k)).surjective x
  change y ∈ peuClassSubmodule I ↔
    (linearClassEquiv (k := k)).symm (linearClassEquiv y) ∈ extendedUnitSubspace hζ k roots A
  rw [Equiv.symm_apply_apply, peuClassSubmodule_eq_extendedUnitSubspace K C A hζ k p]

end LocalClassFieldTheory

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaScalarCharacter
public import FLT.AbsoluteGaloisGroup.RootCharacterExponent
public import FLT.GaloisRepresentation.SerreWeight.ScalarCharacterRoots
public import FLT.Deformations.RepresentationTheory.ScalarActionCharpoly

/-!
# Actual niveau-two characters of simple prime-field inertia actions

Extract a residue-root-valued character with the same kernel as the given
representation and prove its two conjugates give every characteristic
polynomial. This does not yet compare its kernel with the root character
of a specified uniformizer.
-/

@[expose] public noncomputable section
namespace LocalRamification
open NumberField IsLocalRing GaloisRepresentation.SerreWeight Polynomial

universe u
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure (v.adicCompletion K)
local notation "k" => ResidueField (IntegralClosure O Ω)
variable {V : Type u} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  (ρ : Representation (ZMod p) (localInertiaGroup v) V) [ρ.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) V)ˣ]
  [DiscreteTopology (Module.End (ZMod p) V)ˣ]

/-- The absolute residue field has the original residue characteristic. -/
local instance inertiaCharacterResidueCharP : CharP k p :=
  charP_of_injective_ringHom
    (ResidueField.map (algebraMap O (IntegralClosure O Ω))).injective p

/-- The two actual inertia eigencharacters are extracted, with an open unchanged kernel. -/
theorem exists_niveauTwo_inertia_character (hρ : Continuous ρ.toHomUnits)
    (hV : Module.finrank (ZMod p) V = 2) :
    ∃ χ : localInertiaGroup v →* rootsOfUnity (p * p - 1) k,
      χ.ker = ρ.toHomUnits.ker ∧ IsOpen (χ.ker : Set (localInertiaGroup v)) ∧
      χ ^ p ≠ χ ∧ ∀ g,
        (ρ g).charpoly.map (ZMod.castHom (dvd_refl p) k) =
          (X - C ((χ g : kˣ) : k)) * (X - C (((χ g : kˣ) : k) ^ p)) := by
  obtain ⟨F, hF, hfin, hp, hmod, χ, hdim, hcard, hχ, hker, hne⟩ :=
    exists_niveauTwo_scalar_character v p ρ hρ hV
  let : IsAlgClosed k := LocalRoot.residue_isAlgClosed v
  let : Algebra (ZMod p) F := (ZMod.castHom (dvd_refl p) F).toAlgebra
  let : Algebra (ZMod p) k := (ZMod.castHom (dvd_refl p) k).toAlgebra
  let ε : F →+* k := (IsSepClosed.lift (K := ZMod p) (L := F) (M := k)).toRingHom
  have hc : Nat.card F - 1 = p * p - 1 := congrArg (· - 1) hcard
  let ψ := (scalarUnitsToRoots ε hc).comp χ
  have hk : ψ.ker = ρ.toHomUnits.ker :=
    (scalarUnitsToRoots_comp_ker ε hc χ).trans hker
  refine ⟨ψ, hk, ?_, scalarUnitsToRoots_comp_frobenius_ne ε hc χ hne, fun g ↦ ?_⟩
  · rw [hk]
    exact hρ.isOpen_preimage _ (isOpen_discrete {1})
  · have hf := (ρ g).charpoly_rank_two_scalar_factors hdim (χ g : F) (hχ g) ε hV
    have he : ε.comp (ZMod.castHom (dvd_refl p) F) = ZMod.castHom (dvd_refl p) k :=
      Subsingleton.elim _ _
    rw [he] at hf
    exact hf

end LocalRamification

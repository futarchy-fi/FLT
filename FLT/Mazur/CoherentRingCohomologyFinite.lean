/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleRingCohomologyExact
public import FLT.Mazur.CoherentGenericRankOneCriterion

/-!
# Finite base-ring cohomology and coherent dévissage

The coefficient ring need not be a field. Noetherianity makes finite
cohomology a two-out-of-three property, so geometric rank-one witnesses
suffice. Construction of proper-scheme witnesses is a separate obligation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ZeroObject
open FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.FCurve

local instance finiteRingHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))

/-- Every actual coefficient cohomology module is finite over the specified ring. -/
def HasFiniteRingCohomology (M : X.Modules) : Prop :=
  ∀ n : ℕ, Module.Finite R (ModuleRingH ρ M n)

/-- A zero coefficient has finite cohomology over any commutative ring. -/
theorem hasFiniteRingCohomology_of_isZero (M : X.Modules) (hM : IsZero M) :
    HasFiniteRingCohomology ρ M := by
  intro n
  have hz : IsZero (moduleAbelianSheaf M) := (moduleToSheaf X).map_isZero hM
  let : Subsingleton (ModuleRingH ρ M n) := Sheaf.subsingleton_H_of_isZero hz n
  infer_instance

/-- Coefficient isomorphisms preserve finite cohomology with the same ring action. -/
theorem hasFiniteRingCohomology_iso {M N : X.Modules} (e : M ≅ N) :
    HasFiniteRingCohomology ρ M ↔ HasFiniteRingCohomology ρ N := by
  constructor
  · intro h n
    let : Module.Finite R ((moduleRingHFunctor ρ n).obj M) := h n
    exact Module.Finite.equiv ((moduleRingHFunctor ρ n).mapIso e).toLinearEquiv
  · intro h n
    let : Module.Finite R ((moduleRingHFunctor ρ n).obj N) := h n
    exact Module.Finite.equiv ((moduleRingHFunctor ρ n).mapIso e.symm).toLinearEquiv

/-- Empty schemes require no geometric witness or Noetherian assumption. -/
theorem hasFiniteRingCohomology_of_isEmpty [IsEmpty X] (M : X.Modules) :
    HasFiniteRingCohomology ρ M :=
  hasFiniteRingCohomology_of_isZero ρ M
    ((isZero_iff_stalk_isZero M).mpr fun x ↦ isEmptyElim x)

variable [IsNoetherianRing R]

/-- All three directions of coherent two-out-of-three over a Noetherian ring. -/
theorem hasFiniteRingCohomology_twoOutOfThree :
    TwoOutOfThree (HasFiniteRingCohomology ρ) where
  left {S} hS h₂ h₃ n := by
    cases n with
    | zero =>
      let : Module.Finite R ((moduleRingHFunctor ρ 0).obj S.X₂) := h₂ 0
      exact moduleRingH_finite_left_zero ρ S hS.shortExact
    | succ n =>
      let : Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₃) := h₃ n
      let : Module.Finite R ((moduleRingHFunctor ρ (n + 1)).obj S.X₂) := h₂ (n + 1)
      exact moduleRingH_finite_left_succ ρ S hS.shortExact n
  middle {S} hS h₁ h₃ n := by
    let : Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₁) := h₁ n
    let : Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₃) := h₃ n
    exact moduleRingH_finite_middle ρ S hS.shortExact n
  right {S} hS h₁ h₂ n := by
    let : Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₂) := h₂ n
    let : Module.Finite R ((moduleRingHFunctor ρ (n + 1)).obj S.X₁) := h₁ (n + 1)
    exact moduleRingH_finite_right ρ S hS.shortExact n

/-- Rank-one witness dévissage applies to base-ring finite cohomology. -/
theorem coherent_hasFiniteRingCohomology_of_witnesses [IsNoetherian X]
    (hw : HasGenericRankOneWitnesses (HasFiniteRingCohomology ρ))
    (M : X.Modules) [M.IsFinitePresentation] : HasFiniteRingCohomology ρ M :=
  generic_rank_one_of_zero (hasFiniteRingCohomology_twoOutOfThree ρ) hw
    (hasFiniteRingCohomology_of_isZero ρ 0 (isZero_zero _)) M

end FLT.Mazur.FCurve

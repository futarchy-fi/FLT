/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedCoefficientSequence
public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

/-!
# Shapiro vanishing for the concrete coefficient module

The orbit-function coefficient module is coinduction from the trivial subgroup.
For finite groups it is also induction, so both positive cohomology and positive
homology vanish without any freeness assumption on the coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G)

/-- The concrete functions are coinduction from the trivial subgroup. -/
def coinducedCoefficientsIso : coinducedCoefficients M ≅
    Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) M) where
  hom := Rep.ofHom ⟨{
    toFun f := ⟨f, by intro g x; simp [Subgroup.mem_bot.mp g.property]⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }, fun _ => by ext; rfl⟩
  inv := Rep.ofHom ⟨(Representation.coindV (⊥ : Subgroup G).subtype
    (Rep.trivial k (⊥ : Subgroup G) M).ρ).subtype, fun _ => by ext; rfl⟩

/-- Positive ordinary cohomology of the concrete coinduced module vanishes. -/
theorem coinducedCoefficients_cohomology_isZero (n : ℕ) :
    Limits.IsZero (groupCohomology (coinducedCoefficients M) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
    (Rep.trivial k (⊥ : Subgroup G) M) n).of_iso
      ((groupCohomology.functor k G (n + 1)).mapIso (coinducedCoefficientsIso M) ≪≫
        groupCohomology.coindIso _ (n + 1))

/-- Positive ordinary homology of the concrete coinduced module vanishes. -/
theorem coinducedCoefficients_homology_isZero [Finite G] (n : ℕ) :
    Limits.IsZero (groupHomology (coinducedCoefficients M) (n + 1)) := by
  classical
  exact (isZero_groupHomology_succ_of_subsingleton
    (Rep.trivial k (⊥ : Subgroup G) M) n).of_iso
      ((groupHomology.functor k G (n + 1)).mapIso
        (coinducedCoefficientsIso M ≪≫ (Rep.indCoindIso _).symm) ≪≫
          groupHomology.indIso _ _ (n + 1))

end LocalClassFieldTheory

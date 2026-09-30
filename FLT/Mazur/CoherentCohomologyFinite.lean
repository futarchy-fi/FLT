/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomologyExact
public import FLT.Mazur.ModuleStalkExact

/-!
# The finite-cohomology property for coherent dévissage

Finiteness in every degree is a two-out-of-three property of coherent module
sheaves. The left degree-zero endpoint uses injectivity, while positive degrees
use the preceding quotient cohomology group. These formal statements do not
assert finiteness for proper schemes or construct the generic-rank-one witnesses.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

local instance finiteCohomologyHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Every cohomology group of the specified coefficient is finite over the base field. -/
def HasFiniteCohomology (M : X.Modules) : Prop :=
  ∀ n : ℕ, Module.Finite k (ModuleScalarH f M n)

/-- Forgetting scalars takes an actual module short exact sequence to the complex
used by the scalar cohomology long exact sequence. -/
lemma moduleAbelianComplex_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (moduleAbelianComplex S).ShortExact :=
  CoherentDevissage.moduleToSheaf_shortExact hS

/-- All-degree finiteness satisfies coherent two-out-of-three, including degree zero. -/
theorem hasFiniteCohomology_twoOutOfThree :
    CoherentDevissage.TwoOutOfThree (HasFiniteCohomology f) where
  left {S} hS h₂ h₃ n := by
    have h := moduleAbelianComplex_shortExact hS.shortExact
    cases n with
    | zero =>
      let := h₂ 0
      exact moduleScalarH_finite_left_zero S h f
    | succ n =>
      let := h₃ n
      let := h₂ (n + 1)
      exact moduleScalarH_finite_left_succ S h f n
  middle {S} hS h₁ h₃ n := by
    let := h₁ n
    let := h₃ n
    exact moduleScalarH_finite_middle S (moduleAbelianComplex_shortExact hS.shortExact) f n
  right {S} hS h₁ h₂ n := by
    let := h₂ n
    let := h₁ (n + 1)
    exact moduleScalarH_finite_right S (moduleAbelianComplex_shortExact hS.shortExact) f n

/-- Zero coefficients have finite cohomology without any geometric hypotheses. -/
theorem hasFiniteCohomology_of_isZero (M : X.Modules) (hM : IsZero M) :
    HasFiniteCohomology f M := by
  intro n
  have hz : IsZero (moduleAbelianSheaf M) :=
    (CoherentDevissage.moduleToSheaf X).map_isZero hM
  let : Subsingleton (ModuleScalarH f M n) := Sheaf.subsingleton_H_of_isZero hz n
  infer_instance

/-- Finite cohomology is unchanged by an isomorphism of the actual coefficient sheaves. -/
theorem hasFiniteCohomology_iso {M N : X.Modules} (e : M ≅ N) :
    HasFiniteCohomology f M ↔ HasFiniteCohomology f N := by
  constructor
  · intro h n
    let : Module.Finite k ((moduleScalarHFunctor f n).obj M) := h n
    exact Module.Finite.equiv ((moduleScalarHFunctor f n).mapIso e).toLinearEquiv
  · intro h n
    let : Module.Finite k ((moduleScalarHFunctor f n).obj N) := h n
    exact Module.Finite.equiv ((moduleScalarHFunctor f n).mapIso e.symm).toLinearEquiv

end FLT.Mazur.FCurve

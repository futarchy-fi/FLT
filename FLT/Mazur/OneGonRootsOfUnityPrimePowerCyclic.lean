/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonRootsOfUnitySubgroup
public import FLT.Mazur.TorusRootsOfUnityPrimePowerCyclic

/-!
# Cyclic nonetale boundary subgroups on the original one-gon

The original pinched curve carries the actual prime-power roots-of-unity
subgroup, with its identity as Cartier generator in characteristic p.
The generator and cyclicity persist on every scheme base change.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.OneGonSmoothing

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)

/-- The original pinched-curve ideal is the full identity thickening. -/
theorem originalRootsOfUnitySubgroup_primePower_ideal (r : ℕ) :
    (originalRootsOfUnitySubgroup K (p ^ r)).ideal = (E).identitySection.left.ker ^ p ^ r :=
  (E).torusRootsOfUnitySubgroup_primePower_ideal (rootsOfUnityTorusIso K) p r

/-- The identity generates the entire prime-power divisor, with multiplicity. -/
theorem originalRootsOfUnitySubgroup_primePower_generator (r : ℕ) :
    (originalRootsOfUnitySubgroup K (p ^ r)).IsCartierGenerator 1 :=
  (E).torusRootsOfUnitySubgroup_primePower_generator (rootsOfUnityTorusIso K) p r

/-- These original singular-curve subgroups satisfy the actual cyclic level condition. -/
theorem originalRootsOfUnitySubgroup_primePower_isCyclic (r : ℕ) :
    (originalRootsOfUnitySubgroup K (p ^ r)).IsCyclic :=
  (E).torusRootsOfUnitySubgroup_primePower_isCyclic (rootsOfUnityTorusIso K) p r

/-- The coincident Cartier generator survives arbitrary tests of the original one-gon. -/
theorem originalRootsOfUnitySubgroup_primePower_baseChange_generator (r : ℕ)
    {T : Scheme} (g : T ⟶ Spec (.of K)) :
    ((originalRootsOfUnitySubgroup K (p ^ r)).baseChange g).IsCartierGenerator
      ((originalRootsOfUnitySubgroup K (p ^ r)).pullGenerator g 1) :=
  (originalRootsOfUnitySubgroup_primePower_generator K p r).baseChange _ g

/-- Arbitrary, including nonreduced, tests retain cyclicity. -/
theorem originalRootsOfUnitySubgroup_primePower_baseChange_isCyclic (r : ℕ)
    {T : Scheme} (g : T ⟶ Spec (.of K)) :
    ((originalRootsOfUnitySubgroup K (p ^ r)).baseChange g).IsCyclic :=
  (originalRootsOfUnitySubgroup_primePower_isCyclic K p r).baseChange _ g

end FLT.Mazur.OneGonSmoothing

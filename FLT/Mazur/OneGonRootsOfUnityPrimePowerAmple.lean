/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonIdentityDivisorAmple
public import FLT.Mazur.OneGonRootsOfUnityPrimePowerCyclic
public import FLT.Mazur.AmpleCyclicLevel

/-!
# Actual ample cyclic nonetale levels on the original one-gon

The characteristic-p prime-power subgroup is the repeated identity divisor,
whose line is ample. Together with its proved Cartier generator this gives
an actual ample cyclic level, retained on arbitrary scheme base changes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonSmoothing

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The actual prime-power subgroup divisor on the original one-gon is relatively ample. -/
theorem originalRootsOfUnitySubgroup_primePower_isAmple (r : ℕ) :
    (originalRootsOfUnitySubgroup K (p ^ r)).IsAmple := by
  refine ⟨(originalRootsOfUnitySubgroup_relativeCartier K (p ^ r)).1, ?_⟩
  exact (originalOneGon_identityPowerAmple K (p ^ r) (NeZero.pos (p ^ r))).of_iso
    (FCurve.divisorLineBundleEqIso
      (originalRootsOfUnitySubgroup_primePower_ideal K p r) _ _)

/-- The constructed subgroup and original curve define a genuine ample cyclic level. -/
def originalRootsOfUnityPrimePowerLevel (r : ℕ) :
    GeneralizedEllipticCurve.FiniteSubgroup.ampleCyclicLevels (Spec (.of K)) (p ^ r) :=
  ⟨⟨_, originalRootsOfUnitySubgroup K (p ^ r)⟩,
    originalRootsOfUnitySubgroup_primePower_isCyclic K p r,
    originalRootsOfUnitySubgroup_primePower_isAmple K p r⟩

/-- Every scheme test retains both the cyclic and ample level conditions. -/
theorem originalRootsOfUnitySubgroup_primePower_baseChange_level (r : ℕ)
    {T : Scheme} (g : T ⟶ Spec (.of K)) :
    ((originalRootsOfUnitySubgroup K (p ^ r)).baseChange g).IsCyclic ∧
      ((originalRootsOfUnitySubgroup K (p ^ r)).baseChange g).IsAmple :=
  ⟨originalRootsOfUnitySubgroup_primePower_baseChange_isCyclic K p r g,
    (originalRootsOfUnitySubgroup_primePower_isAmple K p r).baseChange g⟩

end FLT.Mazur.OneGonSmoothing

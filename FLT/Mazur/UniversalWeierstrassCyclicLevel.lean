/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicSubgroup
public import FLT.Mazur.SmoothFiniteSubgroupAmple
public import FLT.Mazur.AmpleCyclicClassPresheaf

/-!
# The actual ample cyclic level on the universal auxiliary family

The constructed Cartier subgroup has positive rank on every fiber of the
smooth geometrically integral cubic. Its divisor is therefore relatively
ample. This gives actual level data and its isomorphism class; it does not
identify the coefficient parameter scheme with the modular curve.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open GeneralizedEllipticCurve.FiniteSubgroup

variable (p : ℕ) [NeZero p]

/-- Geometric integrality of the original cubic survives this parameter base change. -/
instance cyclicFamily_geometricallyIntegral : GeometricallyIntegral (cyclicFamily p).curve.hom := by
  change GeometricallyIntegral
    (CategoryTheory.Limits.pullback.snd
      (WeierstrassIntegralChart.integralCurveStructure smoothEquation)
      (cyclicAuxiliaryScheme p).hom)
  infer_instance

/-- The universal cyclic Cartier divisor is relatively ample over the whole parameter base. -/
theorem cyclicSubgroup_isAmple : (cyclicSubgroup p).IsAmple :=
  (cyclicSubgroup p).isAmple_of_smooth (NeZero.pos p) (cyclicSubgroup_relativeCartier p).1

/-- Actual ample cyclic data on the original marked family. -/
def cyclicLevel : ampleCyclicLevels (cyclicAuxiliaryScheme p).left p :=
  ⟨⟨cyclicFamily p, cyclicSubgroup p⟩, cyclicSubgroup_isCyclic p, cyclicSubgroup_isAmple p⟩

/-- The isomorphism class furnished by the parameterized universal marked cubic. -/
def cyclicModuliClass :
    ampleCyclicClasses (cyclicAuxiliaryScheme p).left p :=
  Quotient.mk _ (cyclicLevel p)

/-- Forgetting cyclicity and ampleness retains the constructed subgroup in the original family. -/
theorem cyclicModuliClass_forget :
    ampleCyclicClassesForget (cyclicAuxiliaryScheme p).left p
      (cyclicModuliClass p) =
        Quotient.mk (compatibleIsoSetoid
          (cyclicAuxiliaryScheme p).left p) ⟨cyclicFamily p, cyclicSubgroup p⟩ := rfl

end FLT.Mazur.UniversalWeierstrass

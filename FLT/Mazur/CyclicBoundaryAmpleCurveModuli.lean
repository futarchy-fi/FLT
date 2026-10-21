/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleCurveTransport
public import FLT.Mazur.CyclicBoundaryAmpleBaseChange

/-!
# Ample transport preserves the full modular family

The scheme comparison induced by a generalized-curve isomorphism identifies
actual universal subgroups, so its modular square commutes on all scheme tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S}
  [IsSeparated E.group.hom] [IsSeparated F.group.hom]
  [SmoothOfRelativeDimension 1 E.group.hom] [SmoothOfRelativeDimension 1 F.group.hom]
  (e : E ≅ F) (n : ℕ) [NeZero n]

/-- The ample comparison preserves the actual structure morphism over the common base. -/
@[reassoc] theorem ampleCurveTransport_base :
    ampleCurveTransport e n ≫ ampleParameterBase F n = ampleParameterBase E n := by
  change ampleCurveTransport e n ≫ (ampleParameterOpen F n).ι ≫
    (cyclicFaithfulParameter F.group n).hom = _
  rw [ampleCurveTransport_inclusion_assoc, (faithfulCurveTransportIso e n).hom.w]
  rfl

/-- Ample transport preserves the actual universal full curve and subgroup. -/
def ampleCurveTransportSubgroupIso :
    CompatibleIso (ampleUniversalLevel E n).val.2
      ((ampleUniversalLevel F n).val.2.baseChange (ampleCurveTransport e n)) := by
  have c := faithfulTransportTestSubgroupIso e n (ampleParameterOpen E n).ι
  rw [← ampleCurveTransport_inclusion e n] at c
  exact c.trans ((faithfulUniversalSubgroup F n).compatibleBaseChangeComp
    (ampleParameterOpen F n).ι (ampleCurveTransport e n))

/-- The actual universal level class is unchanged under full curve transport. -/
theorem ampleUniversalClass_curveTransport :
    ampleUniversalClass E n = ampleCyclicClassesPullback (ampleCurveTransport e n) n
      (ampleUniversalClass F n) :=
  Quotient.sound ⟨ampleCurveTransportSubgroupIso e n⟩

/-- Full curve transport commutes with the modular transformation on every scheme test. -/
theorem ampleModuliMap_curveTransport :
    ampleModuliMap E n = uliftYoneda.map (ampleCurveTransport e n) ≫ ampleModuliMap F n := by
  ext T u
  change ampleCyclicClassesPullback u.down n (ampleUniversalClass E n) =
    ampleCyclicClassesPullback (u.down ≫ ampleCurveTransport e n) n (ampleUniversalClass F n)
  rw [ampleUniversalClass_curveTransport e n, ampleCyclicClassesPullback_comp]
  rfl

end FLT.Mazur.CyclicBoundaryParameter

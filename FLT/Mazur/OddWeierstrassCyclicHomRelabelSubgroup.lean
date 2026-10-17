/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomRelabelCurve
public import FLT.Mazur.OddWeierstrassCyclicHomSourceModuli

/-!
# Odd characteristic chart: relabeling retains the entire cyclic Cartier subgroup

The full curve comparison preserves the product ideal with every repeated
factor. Transporting the actual original subgroup therefore proves the
relabeled multiplication equation, without a distinctness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (a : MulAut (Labels 3))
  (c : MulAut (Multiplicative (ZMod n))) {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "fN" => f ≫ Over.Hom.left (cyclicHomRelabel n a c)

variable (h : cyclicHomMultiplicationEquation n f = 0)

/-- Transporting the original subgroup gives precisely the relabeled orbit ideal. -/
theorem cyclicHomRelabel_retained_ideal :
    ((cyclicHomSubgroup n f h).transport (cyclicHomRelabelCurveIso n a c f).symm).ideal =
      cyclicHomSourceIdeal n fN := by
  let H := cyclicHomSubgroup n f h
  let j := H.transportCompatibleIso (cyclicHomRelabelCurveIso n a c f).symm
  have hi := ideal_transport H _ j.curve j.subgroup j.compatible
  change _ = H.ideal.comap (cyclicHomRelabelCurveIso n a c f).hom.curve.left at hi
  rw [show H.ideal = cyclicHomSourceIdeal n f from cyclicHomSubgroup_ideal n f h] at hi
  exact hi.trans (cyclicHomRelabel_ideal n a c f).symm

include h in
/-- Every original subgroup parameter relabels to another actual subgroup parameter. -/
theorem cyclicHomRelabel_equation : cyclicHomMultiplicationEquation n fN = 0 :=
  cyclicHomMultiplicationEquation_of_subgroup n fN
    ((cyclicHomSubgroup n f h).transport (cyclicHomRelabelCurveIso n a c f).symm)
    (cyclicHomRelabel_retained_ideal n a c f h)

/-- The full relabeled subgroup is compatibly isomorphic to the full original subgroup. -/
def cyclicHomRelabelSubgroupIso :
    CompatibleIso (cyclicHomSubgroup n fN (cyclicHomRelabel_equation n a c f h))
      (cyclicHomSubgroup n f h) :=
  (compatibleIsoOfIdealEq _ _ ((cyclicHomSubgroup_ideal n _ _).trans
    (cyclicHomRelabel_retained_ideal n a c f h).symm)).trans
      ((cyclicHomSubgroup n f h).transportCompatibleIso
        (cyclicHomRelabelCurveIso n a c f).symm).symm

/-- Relabeling preserves the actual ample cyclic modular class. -/
theorem cyclicHomSourceModuliClass_relabel :
    cyclicHomSourceModuliClass n fN (cyclicHomRelabel_equation n a c f h) =
      cyclicHomSourceModuliClass n f h :=
  Quotient.sound ⟨cyclicHomRelabelSubgroupIso n a c f h⟩

end FLT.Mazur.OddWeierstrassParameter

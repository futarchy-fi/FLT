/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomRelabelParameter
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq
public import FLT.Mazur.CyclicMarkingDivisorTransport
public import FLT.Mazur.CyclicMarkingRelabelIdeal

/-!
# Odd characteristic chart: relabeling compares the whole curve and cyclic orbit ideal

The coefficient map is unchanged. Its full curve comparison carries each
relabeled section to the corresponding original section, preserving every
factor of the cyclic Cartier ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n)))
  {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "fR" => f ≫ Over.Hom.left (cyclicHomRelabel n a c)

/-- The relabeled source uses exactly the original coefficient map. -/
theorem cyclicHomRelabel_source_base :
    cyclicHomAuxiliaryPoint n fR ≫ levelThree.hom =
      cyclicHomAuxiliaryPoint n f ≫ levelThree.hom := by
  simp only [cyclicHomAuxiliaryPoint, Category.assoc, (cyclicHomAuxiliary n).w,
    cyclicHomRelabel_base]

/-- Relabeling compares the full original smooth source curves. -/
def cyclicHomRelabelCurveIso : cyclicHomSourceCurve n fR ≅ cyclicHomSourceCurve n f :=
  (baseChangeCongr (cyclicHomRelabel_source_base n a c f)).app universalCurve

/-- The curve comparison retains the universal group projection. -/
@[reassoc] theorem cyclicHomRelabelCurveIso_fst :
    (cyclicHomRelabelCurveIso n a c f).hom.group.left ≫
      pullback.fst universalGroup.hom (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom) =
        pullback.fst universalGroup.hom (cyclicHomAuxiliaryPoint n fR ≫ levelThree.hom) :=
  baseChangeCongr_group_fst universalCurve (cyclicHomRelabel_source_base n a c f)

/-- Every original cyclic value is retained under the prescribed label permutation. -/
theorem cyclicHomRelabelCurveIso_marking (i : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n fR i ≫ (cyclicHomRelabelCurveIso n a c f).hom.group =
      cyclicHomSourceMarking n f (c.symm i) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (cyclicHomSourceMarking n fR i ≫
      (cyclicHomRelabelCurveIso n a c f).hom.group).left ≫
        pullback.fst universalGroup.hom (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom) = _
    rw [Over.comp_left, Category.assoc, cyclicHomRelabelCurveIso_fst,
      cyclicHomSourceMarking_fst, cyclicHomSourceMarking_fst, Category.assoc]
    exact congrArg (fun g ↦ f ≫ g.left) (cyclicHomRelabel_value n a c i)
  · exact (cyclicHomSourceMarking n fR i ≫
      (cyclicHomRelabelCurveIso n a c f).hom.group).w.trans
        (cyclicHomSourceMarking n f (c.symm i)).w.symm

/-- The relabeled full orbit ideal is the original ideal under the actual curve comparison. -/
theorem cyclicHomRelabel_ideal : cyclicHomSourceIdeal n fR =
    (cyclicHomSourceIdeal n f).comap (cyclicHomRelabelCurveIso n a c f).hom.curve.left := by
  have hm (i : Multiplicative (ZMod n)) :
      cyclicHomSourceMarking n f (c.symm i) ≫ (cyclicHomRelabelCurveIso n a c f).inv.group =
        cyclicHomSourceMarking n fR i := by
    rw [← cyclicHomRelabelCurveIso_marking n a c f i]
    change (_ ≫ (groupIso (cyclicHomRelabelCurveIso n a c f)).hom) ≫
      (groupIso (cyclicHomRelabelCurveIso n a c f)).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hi := cyclicMarkingIdeal_transport
    ((cyclicHomSourceMarking n f).comp c.symm.toMonoidHom) (cyclicHomSourceMarking n fR)
    (cyclicHomRelabelCurveIso n a c f).symm hm
  rw [cyclicMarkingIdeal_relabel] at hi
  exact hi

end FLT.Mazur.OddWeierstrassParameter

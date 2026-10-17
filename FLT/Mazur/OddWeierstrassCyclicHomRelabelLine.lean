/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomRelabelCurve
public import FLT.Mazur.DivisorLineTensorSectionCompatibility
public import FLT.Mazur.CartierIdealPullbackComparison

/-!
# Odd characteristic chart: relabeling preserves the entire cyclic divisor line and its section

The comparison uses the full product ideal, including repeated factors on
non-etale fibers. Its canonical vanishing section and every tensor power
are preserved on arbitrary test schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open FCurve
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLinePullbackIsoOfEq
variable (n : ℕ) [NeZero n] (a : MulAut (Labels 3))
  (c : MulAut (Multiplicative (ZMod n))) {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "fR" => f ≫ Over.Hom.left (cyclicHomRelabel n a c)
local notation "r" => Over.Hom.left (Iso.hom
  (GeneralizedEllipticCurve.curveIso (cyclicHomRelabelCurveIso n a c f)))

/-- The actual cyclic orbit divisor determines its positive invertible sheaf. -/
def cyclicHomSourceLine : (cyclicHomSourceCurve n f).curve.left.Modules :=
  divisorLineBundle (cyclicHomSourceIdeal n f) (cyclicHomSourceIdeal_cartier n f).1

/-- The full ideal pullback comparison is invertible under relabeling. -/
theorem cyclicHomRelabelIdealComparison_isIso :
    IsIso (idealModulePullbackHom (cyclicHomSourceIdeal n f) r) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (cyclicHomSourceIdeal_cartier n f).1
  change EffectiveCartier ((cyclicHomSourceIdeal n f).comap
    (cyclicHomRelabelCurveIso n a c f).hom.curve.left)
  rw [← cyclicHomRelabel_ideal n a c f]
  exact (cyclicHomSourceIdeal_cartier n fR).1

/-- The actual full curve comparison identifies the original divisor lines. -/
irreducible_def cyclicHomRelabelLineIso :
    (Scheme.Modules.pullback r).obj (cyclicHomSourceLine n f) ≅
      cyclicHomSourceLine n fR := by
  let _ := cyclicHomRelabelIdealComparison_isIso n a c f
  exact divisorLinePullbackIsoOfEq r (cyclicHomSourceIdeal_cartier n f).1
    (cyclicHomSourceIdeal_cartier n fR).1 (cyclicHomRelabel_ideal n a c f).symm

/-- The canonical vanishing section is retained by the exact original line comparison. -/
theorem cyclicHomRelabelLineIso_section :
    DivisorLineSectionCompatible r (cyclicHomSourceIdeal_cartier n f).1
      (cyclicHomSourceIdeal_cartier n fR).1 (cyclicHomRelabelLineIso n a c f) := by
  let _ := cyclicHomRelabelIdealComparison_isIso n a c f
  rw [cyclicHomRelabelLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Every tensor power retains its powered canonical section, including degree zero. -/
theorem cyclicHomRelabelLineIso_power_section (d : ℕ) :
    DivisorLinePowerSectionCompatible r (cyclicHomSourceIdeal_cartier n f).1
      (cyclicHomSourceIdeal_cartier n fR).1 (cyclicHomRelabelLineIso n a c f) d :=
  (cyclicHomRelabelLineIso_section n a c f).tensorPower_section d

end FLT.Mazur.OddWeierstrassParameter

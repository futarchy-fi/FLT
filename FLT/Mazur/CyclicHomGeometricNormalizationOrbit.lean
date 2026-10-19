/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomGeometricMarkedComparison
public import FLT.Mazur.CyclicHomMarkedFamilyRelation
public import FLT.Mazur.CyclicHomRelabelAuxiliaryMarking

/-!
# Geometric full comparisons give equality of relabeled normalized parameters

Align both original markings using the given compatible comparison, then use
marked rigidity. The result is equality of the full parameter morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {K : Type} [Field K] [IsAlgClosed K]
  (f g : Spec (.of K) ⟶ (cyclicHomAuxiliaryScheme n).left)
  (hf : cyclicHomMultiplicationEquation n f = 0)
  (hg : cyclicHomMultiplicationEquation n g = 0)

/-- Every full geometric comparison identifies normalized parameters after finite relabeling. -/
theorem cyclicHom_geometric_normalized_orbit
    (a : CompatibleIso (cyclicHomSubgroup n f hf) (cyclicHomSubgroup n g hg)) :
    ∃ (r : MulAut (Labels 4)) (c : MulAut (Multiplicative (ZMod n))),
      cyclicHomNormalizedPoint n (f ≫ (cyclicHomRelabel n r c).left) =
        cyclicHomNormalizedPoint n g := by
  obtain ⟨r, c, hr, hc⟩ := cyclicHom_geometric_marking_relabel n f g hf hg a
  refine ⟨r.symm, c.symm, ?_⟩
  let fR := f ≫ (cyclicHomRelabel n r.symm c.symm).left
  let b := cyclicHomRelabelCurveIso n r.symm c.symm f ≪≫ a.curve
  let _ : IsMonHom (groupIso b).hom := inferInstanceAs (IsMonHom b.hom.group)
  let e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n fR) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) := CommGrp.mkIso' (groupIso b)
  apply (cyclicHomMarkedFamilyRelated_iff_normalized_eq n fR g).mp
  refine ⟨e, ?_, ?_⟩
  · intro i
    change auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fR) i ≫
      ((cyclicHomRelabelCurveIso n r.symm c.symm f).hom.group ≫ a.curve.hom.group) = _
    rw [← Category.assoc, cyclicHomRelabelCurveIso_auxiliary]
    exact hr i
  · intro i
    change cyclicHomSourceMarking n fR i ≫
      ((cyclicHomRelabelCurveIso n r.symm c.symm f).hom.group ≫ a.curve.hom.group) = _
    rw [← Category.assoc, cyclicHomRelabelCurveIso_marking]
    exact hc i

end FLT.Mazur.UniversalWeierstrass

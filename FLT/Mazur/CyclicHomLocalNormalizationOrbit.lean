/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomLocalMarkedComparison
public import FLT.Mazur.CyclicHomRestrictedMarkedComparison
public import FLT.Mazur.CyclicHomRelabelAuxiliaryMarking

/-!
# Full compatible comparisons give exact local normalized orbits

At invertible level, the original auxiliary and cyclic markings align on one
affine neighborhood. Their actual pulled family comparison and marked rigidity
identify the full normalized parameter morphisms, retaining all nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (hf : cyclicHomMultiplicationEquation n f = 0)
  (hg : cyclicHomMultiplicationEquation n g = 0)
  (a : CompatibleIso (cyclicHomSubgroup n f hf) (cyclicHomSubgroup n g hg))

include a

/-- The exact normalized parameters lie locally in one finite relabeling orbit. -/
theorem cyclicHom_local_normalized_orbit (hn : IsUnit (n : Γ(T, ⊤))) (x : T) :
    ∃ (r : MulAut (Labels 4)) (c : MulAut (Multiplicative (ZMod n))) (U : T.Opens),
      IsAffineOpen U ∧ x ∈ U ∧
      cyclicHomNormalizedPoint n ((U.ι ≫ f) ≫ (cyclicHomRelabel n r c).left) =
        cyclicHomNormalizedPoint n (U.ι ≫ g) := by
  obtain ⟨r, c, U, hU, hx, hr, hc⟩ := cyclicHom_local_marking_relabel n f g hf hg a hn x
  refine ⟨r.symm, c.symm, U, hU, hx, ?_⟩
  let _ : IsAffine U.toScheme := hU
  let _ : IsMonHom (groupIso a.curve).hom :=
    inferInstanceAs (IsMonHom a.curve.hom.group)
  let e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) :=
    CommGrp.mkIso' (groupIso a.curve)
  let d := cyclicHomMarkedIsoPullback n f g e U.ι
  let fU := U.ι ≫ f
  let gU := U.ι ≫ g
  let fR := fU ≫ (cyclicHomRelabel n r.symm c.symm).left
  let b := cyclicHomRelabelCurveIso n r.symm c.symm fU
  let _ : IsMonHom (groupIso b).hom := inferInstanceAs (IsMonHom b.hom.group)
  let eR : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n fR) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n gU) :=
    CommGrp.mkIso' (groupIso b) ≪≫ d
  apply (cyclicHomMarkedFamilyRelated_iff_normalized_eq n fR gU).mp
  refine ⟨eR, ?_, ?_⟩
  · intro i
    change auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fR) i ≫
      (b.hom.group ≫ d.hom.hom.hom.hom) = _
    rw [← Category.assoc, cyclicHomRelabelCurveIso_auxiliary]
    exact cyclicHomMarkedIsoPullback_auxiliary_of_restriction n f g e U.ι (r i) i (hr i)
  · intro i
    change cyclicHomSourceMarking n fR i ≫ (b.hom.group ≫ d.hom.hom.hom.hom) = _
    rw [← Category.assoc, cyclicHomRelabelCurveIso_marking]
    exact cyclicHomMarkedIsoPullback_cyclic_of_restriction n f g e U.ι (c i) i (hc i)

end FLT.Mazur.UniversalWeierstrass

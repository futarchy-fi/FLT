/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalPointPowers
public import FLT.Mazur.PolygonHigherStructureCohomology
public import FLT.Mazur.DivisorPowerHigherVanishing
public import FLT.Mazur.DivisorPowerEulerCharacteristic
public import FLT.Mazur.CurveRiemannRochEuler
public import FLT.Mazur.SectionSumFieldLength

/-!
# Acyclic pole powers at original smooth markings of arbitrary polygons

The exact H0 dimension and genus-one Euler formula kill H1. The actual finite
section divisor propagates higher structure vanishing to every pole power.
This includes reducible polygons and uses the original marking ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonOriginalPointPowers
open FCurve PolygonPinching ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] (E : GeneralizedEllipticCurve (Spec (.of K)))
  (n : ℕ) [NeZero n] (hn : 0 < n)
  (p : components K n ⟶ E.curve) (q : nodes K n ⟶ E.curve)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- The original smooth marking has acyclic positive powers on any split polygon. -/
theorem acyclic (s : 𝟙_ (Over (Spec (.of K))) ⟶ E.group)
    (m : ℕ) (hm : 0 < m) (r : ℕ) :
    Subsingleton (ModuleH (E.smoothMarkingPower s m) (r + 1)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let t := s ≫ E.inclusion
  let hI := (E.smoothMarking_relativeCartier s).1
  let _ : IsFinite (t.left.ker.subschemeι ≫ E.curve.hom) := by
    rw [← sectionImageIso_hom E.curve.hom t.left t.w]
    infer_instance
  cases r with
  | zero =>
    change Subsingleton (ModuleScalarH E.curve.hom (E.smoothMarkingPower s m) 1)
    let _ := (E.smoothMarkingPower_rankOne s m).isFinitePresentation
    let _ := proper_coherent_hasFiniteCohomology E.curve.hom (E.smoothMarkingPower s m) 1
    apply (Module.finrank_zero_iff (R := K)).mp
    have he := curve_riemannRoch_euler E.curve.hom
      (PolygonDimension.dimension K n hn p q h)
      (PolygonConstantSections.constants K n hn p q h) (E.smoothMarkingPower s m)
    have hd : curveSheafDegree E.curve.hom (E.smoothMarkingPower s m) = (m : ℤ) := by
      change curveSheafDegree E.curve.hom (tensorPower (divisorLineBundle t.left.ker hI) m) = _
      rw [curveSheafDegree_divisor_power, divisorFieldLength_section E.curve.hom t.left t.w,
        Nat.cast_one, mul_one]
    rw [hd, PolygonGenusOne.genus_one K n hn p q h, finrank E n hn p q h s m hm] at he
    omega
  | succ r =>
    let _ : Subsingleton (ModuleScalarH E.curve.hom
        (structureModule E.curve.left) (r + 2)) :=
      PolygonHigherStructureCohomology.higher_subsingleton K n hn p q h r
    exact divisorPower_positive_subsingleton E.curve.hom hI (r + 2) (by omega) m

/-- No pinching coordinates need be supplied beyond the geometric classification. -/
theorem acyclic_of_isNeronPolygon (hc : IsNeronPolygon E.curve)
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ E.group) (m : ℕ) (hm : 0 < m) (r : ℕ) :
    Subsingleton (ModuleH (E.smoothMarkingPower s m) (r + 1)) := by
  obtain ⟨n, hn, p, q, h⟩ := hc
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact acyclic E n hn p q h s m hm r

end FLT.Mazur.PolygonOriginalPointPowers

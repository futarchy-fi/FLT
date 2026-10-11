/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleSmoothNonspecialLift
public import FLT.Mazur.FieldNonspecialGeometricCriterion
public import FLT.Mazur.NonspecialDivisorNeighborhood
public import FLT.Mazur.RelativeCartierCurveFinite

/-!
# Smooth local existence of full relative nonspecial divisors

An ample geometric fiber of a proper smooth integral family admits a smooth
pointed base neighborhood carrying a full finite relative Cartier divisor with
acyclic rank-one positive line. The original geometric family square is retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
open CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] [IsAlgClosed k]
  {X Y S : Scheme} [IsIntegral Y] [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  {p : Y ⟶ X} {q : Y ⟶ Spec (.of k)} {g : Spec (.of k) ⟶ S}
  (H : IsPullback p q f g) (B : X.Modules) (hB : LocallyFreeRankOne B)
  (hA : AmpleLineBundle ((Scheme.Modules.pullback p).obj B))

include H hB hA in
/-- Every ample geometric fiber has a smooth pointed neighborhood with a full nonspecial divisor. -/
theorem exists_smooth_nonspecial_divisor_lift :
    ∃ (U Z : Scheme) (a : U ⟶ S) (b : Z ⟶ X) (r : Z ⟶ U)
      (u : Spec (.of k) ⟶ U) (v : Y ⟶ Z) (D : AcyclicRankOneRelativeDivisor r),
      Smooth a ∧ IsPullback b r f a ∧ IsPullback v q r u ∧
      u ≫ a = g ∧ v ≫ b = p ∧ IsFinite (D.val.val.subschemeι ≫ r) := by
  let _ : IsProper q := MorphismProperty.of_isPullback H inferInstance
  let _ : SmoothOfRelativeDimension 1 q := MorphismProperty.of_isPullback H inferInstance
  obtain ⟨U, Z, a, b, r, u, v, M, ha, HA, HV, hu, hv, hM, hV, hR⟩ :=
    exists_smooth_nonspecial_line_lift_of_ample q f H B hB hA
  let _ := ha
  let _ : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian a
  let _ : IsProper r := MorphismProperty.of_isPullback HA inferInstance
  let _ : Flat r := MorphismProperty.of_isPullback HA inferInstance
  let _ : GeometricallyIntegral r := MorphismProperty.of_isPullback HA inferInstance
  let _ : SmoothOfRelativeDimension 1 r := MorphismProperty.of_isPullback HA inferInstance
  have hG := geometricAcyclicRankOne_of_nonspecial q
    ((Scheme.Modules.pullback v).obj M) (hM.pullback v) hA hV hR
  obtain ⟨V, u', v', D, hu', hv', HB, _⟩ :=
    exists_nonspecial_divisor_neighborhood r HV M hM hG
  let HC := (isPullback_morphismRestrict r V).flip
  let _ : SmoothOfRelativeDimension 1 (r ∣_ V) :=
    MorphismProperty.of_isPullback HC inferInstance
  have hD : RelativeEffectiveCartier (r ∣_ V) D.val.val := ⟨D.val.property, D.property.1⟩
  refine ⟨V.toScheme, (r ⁻¹ᵁ V).toScheme, V.ι ≫ a, (r ⁻¹ᵁ V).ι ≫ b,
    r ∣_ V, u', v', D, inferInstance, HC.paste_horiz HA, HB, ?_, ?_, hD.isFinite _⟩
  · rw [← Category.assoc, hu', hu]
  · rw [← Category.assoc, hv', hv]

end FLT.Mazur.FCurve

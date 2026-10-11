/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothNonspecialDivisorCover
public import FLT.Mazur.AcyclicPointedAbelBaseChange

/-!
# Full nonspecial divisor covers on arbitrary original tests

Pull back the constructed small smooth cover along an unrestricted test map.
Every divisor is the full ideal comap of the original relative divisor. The
result applies to nonreduced and non-Noetherian tests and retains their given
cartesian total space, rather than replacing their Picard classes by field data.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
open CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S P T : Scheme} [IsAffine S] [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (B : X.Modules) (hB : AmpleLineBundle B)
  {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (H : IsPullback p q f g)

include hB H in
/-- Arbitrary original tests have a small smooth fppf cover with full nonspecial divisors. -/
theorem exists_nonspecial_divisor_test_cover :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage T,
      (∀ i, Smooth (C.f i)) ∧ ∀ i,
        ∃ (Z : Scheme) (b : Z ⟶ P) (r : Z ⟶ C.X i)
          (D : AcyclicRankOneRelativeDivisor r),
          IsPullback b r q (C.f i) ∧ IsFinite (D.val.val.subschemeι ≫ r) := by
  obtain ⟨C, hC, hD⟩ := exists_smooth_nonspecial_divisor_cover f B hB
  let E := C.pullback₁ g
  refine ⟨E, ?_, ?_⟩
  · intro i
    let _ := hC i
    exact MorphismProperty.pullback_fst (P := @Smooth) g (C.f i) inferInstance
  · intro i
    obtain ⟨Z, b, r, D, HB, _⟩ := hD i
    let _ := hC i
    let _ : IsLocallyNoetherian (C.X i) := LocallyOfFiniteType.isLocallyNoetherian (C.f i)
    let _ : IsProper r := MorphismProperty.of_isPullback HB inferInstance
    let _ : Flat r := MorphismProperty.of_isPullback HB inferInstance
    let _ : GeometricallyIntegral r := MorphismProperty.of_isPullback HB inferInstance
    let _ : SmoothOfRelativeDimension 1 r := MorphismProperty.of_isPullback HB inferInstance
    let a := C.pullbackHom g i
    let Z' := pullback r a
    let j : Z' ⟶ Z := pullback.fst r a
    let r' : Z' ⟶ E.X i := pullback.snd r a
    let HB' : IsPullback j r' r a := IsPullback.of_hasPullback r a
    have w : (j ≫ b) ≫ f = (r' ≫ E.f i) ≫ g := by
      rw [Category.assoc, HB.w, ← Category.assoc j r, HB'.w]
      simpa only [Category.assoc] using congrArg (fun t ↦ r' ≫ t) (C.pullbackHom_map g i)
    let b' : Z' ⟶ P := H.lift (j ≫ b) (r' ≫ E.f i) w
    have Hb : b' ≫ p = j ≫ b := H.lift_fst _ _ _
    have Hq : b' ≫ q = r' ≫ E.f i := H.lift_snd _ _ _
    have HF : IsPullback b' r' q (E.f i) := by
      apply IsPullback.of_right (h₁₂ := p) (h₂₂ := g) (v₁₃ := f) ?_ Hq H
      rw [Hb]
      have ha : a ≫ C.f i = E.f i ≫ g := C.pullbackHom_map g i
      rw [← ha]
      exact HB'.paste_horiz HB
    let D' := acyclicRelativeDivisorPullback HB' D
    let _ : SmoothOfRelativeDimension 1 r' :=
      MorphismProperty.of_isPullback HB' inferInstance
    have hR : RelativeEffectiveCartier r' D'.val.val := ⟨D'.val.property, D'.property.1⟩
    exact ⟨Z', b', r', D', HF, hR.isFinite r'⟩

end FLT.Mazur.FCurve

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NonspecialDivisorTestCover
public import FLT.Mazur.RelativePicardFppfCover

/-!
# Nonspecial divisors in the original Picard pullback convention

The smooth divisor cover supplies full ideals on the exact fiber products
used by the Picard presheaf. Pulling this cover back gives divisors on every
original test, without a Noetherian assumption on that test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
open CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme} [IsAffine S] [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (B : X.Modules) (hB : AmpleLineBundle B)

include hB in
/-- The constructed small cover carries full divisors on the canonical total spaces. -/
theorem exists_canonical_nonspecial_divisor_cover :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage S,
      (∀ i, Smooth (C.f i)) ∧ ∀ i,
        Nonempty (AcyclicRankOneRelativeDivisor (pullback.snd f (C.f i))) := by
  obtain ⟨C, hC, hD⟩ := exists_smooth_nonspecial_divisor_cover f B hB
  refine ⟨C, hC, fun i ↦ ?_⟩
  obtain ⟨Z, b, r, D, H, _⟩ := hD i
  let _ := hC i
  let _ : IsLocallyNoetherian (C.X i) := LocallyOfFiniteType.isLocallyNoetherian (C.f i)
  let _ : IsProper r := MorphismProperty.of_isPullback H inferInstance
  let _ : Flat r := MorphismProperty.of_isPullback H inferInstance
  have H' : IsPullback H.isoPullback.inv (pullback.snd f (C.f i)) r (𝟙 (C.X i)) :=
    IsPullback.of_horiz_isIso ⟨by rw [H.isoPullback_inv_snd, Category.comp_id]⟩
  exact ⟨acyclicRelativeDivisorPullback H' D⟩

include hB in
/-- Every unrestricted original test has canonical full divisors on a small smooth cover. -/
theorem exists_canonical_nonspecial_divisor_test_cover (T : Over S) :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left,
      (∀ i, Smooth (C.f i)) ∧ ∀ i,
        Nonempty (AcyclicRankOneRelativeDivisor
          (pullback.snd f (relativeCoverMember T C i).hom)) := by
  obtain ⟨C, hC, hD⟩ := exists_canonical_nonspecial_divisor_cover f B hB
  let E := C.pullback₁ T.hom
  refine ⟨E, fun i ↦ ?_, fun i ↦ ?_⟩
  · let _ := hC i
    exact MorphismProperty.pullback_fst (P := @Smooth) T.hom (C.f i) inferInstance
  · let _ := hC i
    let _ : IsLocallyNoetherian (C.X i) := LocallyOfFiniteType.isLocallyNoetherian (C.f i)
    let a : relativeCoverMember T E i ⟶ Over.mk (C.f i) :=
      Over.homMk (C.pullbackHom T.hom i) (C.pullbackHom_map T.hom i)
    let _ : IsLocallyNoetherian (Over.mk (C.f i)).left :=
      show IsLocallyNoetherian (C.X i) from inferInstance
    obtain ⟨D⟩ := hD i
    exact ⟨acyclicRelativeDivisorPullback (relativeTotalMap_isPullback f a) D⟩

end FLT.Mazur.FCurve

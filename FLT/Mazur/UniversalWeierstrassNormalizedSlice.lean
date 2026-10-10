/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassNormalizedSliceRing
public import FLT.Mazur.UniversalWeierstrassAuxiliaryEtale

/-!
# The normalized slice of the full auxiliary marking scheme

Pull back the four frame equations to the original faithful level-four space.
This retains its order-four group equations, faithful open, and full scheme
basis. The construction does not replace that space by its affinization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Impose the four frame equations on the actual full auxiliary scheme. -/
def normalizedSlice : Scheme :=
  pullback levelFour.left.toSpecΓ (Spec.map (CommRingCat.ofHom normalizedSliceQuotient))

/-- The actual closed inclusion in the faithful auxiliary marking scheme. -/
def normalizedSliceInclusion : normalizedSlice ⟶ levelFour.left := pullback.fst _ _

instance normalizedSliceInclusion_closed : IsClosedImmersion normalizedSliceInclusion := by
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom normalizedSliceQuotient)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  change IsClosedImmersion (pullback.fst _ _)
  infer_instance

/-- The normalized slice keeps the original arithmetic parameter map. -/
def normalizedSliceOver : Over parameterBase :=
  Over.mk (normalizedSliceInclusion ≫ levelFour.hom)

/-- Forget only normalization, retaining the original complete auxiliary object. -/
def normalizedSliceToAuxiliary : normalizedSliceOver ⟶ levelFour :=
  Over.homMk normalizedSliceInclusion rfl

/-- The full normalized marking, as an actual group homomorphism of scheme sections. -/
def normalizedSliceMarking : Labels 4 →* (normalizedSliceOver ⟶ universalGroup) :=
  AuxiliaryLevel.markingOf universalGroup (Labels 4)
    (normalizedSliceToAuxiliary ≫ auxiliaryInclusion 4)

/-- Every normalized marked section is killed by four in the actual group scheme. -/
theorem normalizedSliceMarking_four (a : Labels 4) : normalizedSliceMarking a ^ 4 = 1 := by
  rw [← map_pow, labels_pow, map_one]

/-- The full marking remains faithful after every nonempty test scheme. -/
theorem normalizedSliceMarking_faithful {U : Over parameterBase}
    (f : U ⟶ normalizedSliceOver) [Nonempty U.left] :
    Function.Injective (AuxiliaryLevel.markingOf universalGroup (Labels 4)
      (f ≫ normalizedSliceToAuxiliary ≫ auxiliaryInclusion 4)) := by
  simpa only [Category.assoc] using
    auxiliaryMarking_injective 4 (f ≫ normalizedSliceToAuxiliary)

/-- The full sixteen-section basis is retained as an actual scheme isomorphism. -/
def normalizedSliceFullBasis :
    (Over.pullback normalizedSliceInclusion).obj (Over.mk auxiliaryConstantLabelsMap) ≅
      (Over.pullback normalizedSliceInclusion).obj (Over.mk auxiliaryFourTorsionMap) :=
  auxiliaryBaseChangedFullBasis normalizedSliceInclusion

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelFour.left)
  (g : AuxiliarySectionRing →+* R)
  (hg : Spec.map (CommRingCat.ofHom g) = f ≫ levelFour.left.toSpecΓ)

/-- Every actual auxiliary point satisfying the frame equations lifts to the full slice. -/
def normalizedSlicePointLift (hn : SatisfiesNormalization g) : Spec (.of R) ⟶ normalizedSlice :=
  pullback.lift f (Spec.map (CommRingCat.ofHom (normalizedSliceLift g hn))) (by
    rw [← Spec.map_comp]
    exact hg.symm)

/-- The lift retains the entire original auxiliary point. -/
@[reassoc] theorem normalizedSlicePointLift_inclusion (hn : SatisfiesNormalization g) :
    normalizedSlicePointLift f g hg hn ≫ normalizedSliceInclusion = f := pullback.lift_fst ..

include hg in
/-- Actual auxiliary points factor uniquely through the slice exactly when normalized. -/
theorem normalizedSlicePoint_iff : SatisfiesNormalization g ↔
    ∃! l : Spec (.of R) ⟶ normalizedSlice, l ≫ normalizedSliceInclusion = f := by
  constructor
  · intro hn
    refine ⟨normalizedSlicePointLift f g hg hn,
      normalizedSlicePointLift_inclusion f g hg hn, ?_⟩
    intro l hl
    exact (cancel_mono normalizedSliceInclusion).mp
      (hl.trans (normalizedSlicePointLift_inclusion f g hg hn).symm)
  · rintro ⟨l, hl, _⟩
    obtain ⟨q, hq⟩ := Spec.map_surjective (l ≫ pullback.snd levelFour.left.toSpecΓ
      (Spec.map (CommRingCat.ofHom normalizedSliceQuotient)))
    have hc : Spec.map q ≫ Spec.map (CommRingCat.ofHom normalizedSliceQuotient) =
        Spec.map (CommRingCat.ofHom g) := by
      rw [hq, Category.assoc, ← pullback.condition, ← Category.assoc]
      change (l ≫ normalizedSliceInclusion) ≫ levelFour.left.toSpecΓ = _
      rw [hl, ← hg]
    have he : CommRingCat.ofHom normalizedSliceQuotient ≫ q = CommRingCat.ofHom g := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      exact hc
    have he' : q.hom.comp normalizedSliceQuotient = g := congrArg CommRingCat.Hom.hom he
    intro i
    rw [← he', RingHom.comp_apply, normalizedSliceQuotient_satisfies i, map_zero]

end FLT.Mazur.UniversalWeierstrass

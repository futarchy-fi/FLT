/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientCartesian

/-!
# The retained smooth embedding after arbitrary coefficient extension

At every finite modification depth, the original coefficient-extended smooth
scheme embeds as exactly the pullback of the retained integral smooth scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open WeierstrassIntegralChart
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (S : Type u) [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "f" => finiteGlobalStructure hπ data j hj

/-- The actual extended original smooth scheme maps into the finite modified family. -/
def finiteGlobalSmoothCoefficientEmbedding :
    (integralSmoothOpen (W.map (algebraMap R S))).toScheme ⟶
      finiteGlobalTensorModel hπ data S j hj :=
  pullback.lift (integralSmoothStructure (W.map (algebraMap R S)))
    (originalSmoothCoefficientMap S W ≫ finiteGlobalSmoothEmbedding hπ data j hj) (by
      simp only [Category.assoc, finiteGlobalSmoothEmbedding_structure]
      exact (originalSmoothCoefficientMap_structure S W).symm)

/-- The embedding retains the coefficient-extended structure map. -/
@[reassoc] theorem finiteGlobalSmoothCoefficientEmbedding_structure :
    finiteGlobalSmoothCoefficientEmbedding S hπ data j hj ≫ pullback.fst q f =
      integralSmoothStructure (W.map (algebraMap R S)) :=
  pullback.lift_fst _ _ _

/-- Projection retains the original integral smooth embedding. -/
@[reassoc] theorem finiteGlobalSmoothCoefficientEmbedding_projection :
    finiteGlobalSmoothCoefficientEmbedding S hπ data j hj ≫ pullback.snd q f =
      originalSmoothCoefficientMap S W ≫ finiteGlobalSmoothEmbedding hπ data j hj :=
  pullback.lift_snd _ _ _

/-- The entire coefficient smooth scheme is Cartesian over the retained integral embedding. -/
theorem finiteGlobalSmoothCoefficientEmbedding_isPullback :
    IsPullback (originalSmoothCoefficientMap S W)
      (finiteGlobalSmoothCoefficientEmbedding S hπ data j hj)
      (finiteGlobalSmoothEmbedding hπ data j hj) (pullback.snd q f) := by
  apply IsPullback.of_bot _
    (finiteGlobalSmoothCoefficientEmbedding_projection S hπ data j hj).symm
    (IsPullback.of_hasPullback q f).flip
  simpa only [finiteGlobalSmoothCoefficientEmbedding_structure,
    finiteGlobalSmoothEmbedding_structure] using
    originalSmoothCoefficientMap_isPullback S W

instance finiteGlobalSmoothCoefficientEmbedding_isOpenImmersion :
    IsOpenImmersion (finiteGlobalSmoothCoefficientEmbedding S hπ data j hj) :=
  MorphismProperty.of_isPullback
    (finiteGlobalSmoothCoefficientEmbedding_isPullback S hπ data j hj)
    (inferInstanceAs (IsOpenImmersion (finiteGlobalSmoothEmbedding hπ data j hj)))

/-- There are no extra points over the retained original smooth scheme after base change. -/
theorem finiteGlobalSmoothCoefficientEmbedding_range :
    Set.range (finiteGlobalSmoothCoefficientEmbedding S hπ data j hj) =
      (pullback.snd q f) ⁻¹' Set.range (finiteGlobalSmoothEmbedding hπ data j hj) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨originalSmoothCoefficientMap S W a,
      (congrArg (fun g => g a)
        (finiteGlobalSmoothCoefficientEmbedding_projection S hπ data j hj)).symm⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, _, hb⟩ := Scheme.exists_preimage_of_isPullback
      (finiteGlobalSmoothCoefficientEmbedding_isPullback S hπ data j hj) a z ha
    exact ⟨b, hb⟩

/-- The original cubic contraction is preserved on all functions. -/
@[reassoc] theorem finiteGlobalSmoothCoefficientEmbedding_contraction :
    finiteGlobalSmoothCoefficientEmbedding S hπ data j hj ≫
        pullback.snd q f ≫ finiteGlobalContraction hπ data j hj =
      (integralSmoothOpen (W.map (algebraMap R S))).ι ≫ integralCoefficientMorphism W := by
  rw [finiteGlobalSmoothCoefficientEmbedding_projection_assoc,
    finiteGlobalSmoothEmbedding_contraction, originalSmoothCoefficientMap_inclusion]

end FLT.Mazur.WeierstrassDividedDepth

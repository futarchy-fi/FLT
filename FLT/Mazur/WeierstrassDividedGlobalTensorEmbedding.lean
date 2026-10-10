/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteFlat
public import FLT.Mazur.WeierstrassDividedFiniteTensorCharts

/-!
# The finite tensor model embeds in the whole projective base change

Base change of the original finite local atlas embedding preserves the
whole local model and its contraction to the original projective cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The actual coefficient pullback of the whole finite projective model. -/
def finiteGlobalTensorModel : Scheme := pullback q (finiteGlobalStructure hπ data j hj)

/-- The entire local tensor model embeds into the actual global tensor model. -/
def finiteLocalTensorEmbedding :
    finiteTensorModel hπ data S j hj ⟶ finiteGlobalTensorModel hπ data S j hj :=
  pullback.map _ _ _ _ (𝟙 _) (finiteLocalChart hπ data j hj) (𝟙 _)
    (by simp) (by simp only [Category.comp_id, finiteLocalChart_structure])

instance finiteLocalTensorEmbedding_isOpenImmersion :
    IsOpenImmersion (finiteLocalTensorEmbedding hπ data S j hj) := by
  unfold finiteLocalTensorEmbedding
  infer_instance

/-- The original local atlas inclusion survives on the entire local tensor model. -/
@[reassoc] theorem finiteLocalTensorEmbedding_square :
    finiteLocalTensorEmbedding hπ data S j hj ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) =
        pullback.snd q (finiteStructure hπ data j hj) ≫ finiteLocalChart hπ data j hj := by
  exact pullback.lift_snd _ _ _

/-- The actual local tensor embedding retains its extended coefficient structure. -/
@[reassoc] theorem finiteLocalTensorEmbedding_structure :
    finiteLocalTensorEmbedding hπ data S j hj ≫
      pullback.fst q (finiteGlobalStructure hπ data j hj) =
        pullback.fst q (finiteStructure hπ data j hj) := by
  simp only [finiteLocalTensorEmbedding, pullback.lift_fst, Category.comp_id]

/-- The local tensor atlas square is cartesian. -/
theorem finiteLocalTensorEmbedding_isPullback :
    IsPullback (finiteLocalTensorEmbedding hπ data S j hj)
      (pullback.snd q (finiteStructure hπ data j hj))
      (pullback.snd q (finiteGlobalStructure hπ data j hj)) (finiteLocalChart hπ data j hj) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _)
    (h₂₂ := finiteGlobalStructure hπ data j hj) _
    (finiteLocalTensorEmbedding_square hπ data S j hj) (.of_hasPullback _ _)
  rw [finiteLocalTensorEmbedding_structure, finiteLocalChart_structure]
  exact .of_hasPullback _ _

/-- The local tensor model covers exactly the full preimage of the original local atlas chart. -/
theorem finiteLocalTensorEmbedding_range :
    Set.range (finiteLocalTensorEmbedding hπ data S j hj) =
      (pullback.snd q (finiteGlobalStructure hπ data j hj)) ⁻¹'
        Set.range (finiteLocalChart hπ data j hj) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨pullback.snd q (finiteStructure hπ data j hj) a,
      congrArg (fun g => g a) (finiteLocalTensorEmbedding_square hπ data S j hj).symm⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb, _⟩ := Scheme.exists_preimage_of_isPullback
      (finiteLocalTensorEmbedding_isPullback hπ data S j hj) z a ha.symm
    exact ⟨b, hb⟩

/-- The original projective-cubic contraction is retained under the global atlas embedding. -/
@[reassoc] theorem finiteLocalTensorEmbedding_toCurve :
    finiteLocalTensorEmbedding hπ data S j hj ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      pullback.snd q (finiteStructure hπ data j hj) ≫ finiteToCurve hπ data j hj := by
  rw [finiteLocalTensorEmbedding_square_assoc, finiteLocalChart_contraction]

end FLT.Mazur.WeierstrassDividedDepth

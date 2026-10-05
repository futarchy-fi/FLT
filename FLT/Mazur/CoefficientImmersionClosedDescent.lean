/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientOpenClosedDescent

/-!
# A quasi-compact immersion becomes closed at a finite coefficient stage

Factor the immersion through its scheme-theoretic image. Its open factor is
closed at the limit, hence at a finite coefficient enlargement. Composing
with the closed image embedding gives the required closed immersion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Approximation

/-- Base change preserves composition of maps with specified base identities. -/
@[reassoc]
lemma immersionBaseChange_comp {Z Q P S T : Scheme.{u}}
    (q : Z ⟶ S) (r : Q ⟶ S) (p : P ⟶ S)
    (a : Z ⟶ Q) (k : Q ⟶ P) (wa : a ≫ r = q) (wk : k ≫ p = r)
    (b : T ⟶ S) :
    immersionBaseChange q r a wa b ≫ immersionBaseChange r p k wk b =
      immersionBaseChange q p (a ≫ k) (by rw [Category.assoc, wk, wa]) b := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- For finite-type coefficient models, closedness of a quasi-compact immersion
at the original ring holds already at a finite enlargement. -/
theorem exists_coefficient_closedImmersion {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Z P : Scheme.{u}} (q : Z ⟶ Spec (.of S₀)) (p : P ⟶ Spec (.of S₀))
    [QuasiCompact p] [LocallyOfFiniteType p]
    (h : Z ⟶ P) [IsImmersion h] [QuasiCompact h] (w : h ≫ p = q)
    (hh : IsClosedImmersion (immersionBaseChange q p h w
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      IsClosedImmersion (immersionBaseChange q p h w
        ((coefficientSpectrumToInitial S₀).app i)) := by
  obtain ⟨Q, a, k, ha, hk, he⟩ :=
    IsImmersion.isImmersion_iff_exists_of_quasiCompact.mp (inferInstance : IsImmersion h)
  let r := k ≫ p
  have wa : a ≫ r = q := by
    change a ≫ (k ≫ p) = q
    rw [← Category.assoc, he, w]
  let ab (T : Scheme.{u}) (b : T ⟶ Spec (.of S₀)) := immersionBaseChange q r a wa b
  let kb (T : Scheme.{u}) (b : T ⟶ Spec (.of S₀)) := immersionBaseChange r p k rfl b
  have hk' (T : Scheme.{u}) (b : T ⟶ Spec (.of S₀)) : IsClosedImmersion (kb T b) :=
    MorphismProperty.of_isPullback (immersionBaseChange_isPullback _ _ _ _ _).flip hk
  have hab (T : Scheme.{u}) (b : T ⟶ Spec (.of S₀)) :
      ab T b ≫ kb T b = immersionBaseChange q p h w b := by
    dsimp only [ab, kb]
    simp only [immersionBaseChange_comp, he]
  have ha' : IsClosedImmersion (ab _ (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) := by
    have : IsClosedImmersion (ab _ (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) ≫
        kb _ (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) := by
      rw [hab]
      exact hh
    exact IsClosedImmersion.of_comp_isClosedImmersion _
      (kb _ (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
  have : QuasiCompact r := inferInstance
  have : LocallyOfFiniteType r := inferInstance
  have hex : ∃ i : (CoefficientStage S₀)ᵒᵖ,
      IsClosedImmersion (ab _ ((coefficientSpectrumToInitial S₀).app i)) := by
    dsimp only [ab] at ha' ⊢
    cases wa
    let := ha
    let := ha'
    exact exists_coefficient_closed_openImmersion S₀ r a
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  rw [← hab]
  exact IsClosedImmersion.comp _ _

end FLT.Mazur.Approximation

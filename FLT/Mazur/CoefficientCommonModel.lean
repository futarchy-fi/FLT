/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientOriginalHomDescent
public import FLT.Mazur.CoefficientIsomorphismDescent
public import FLT.Mazur.CartesianMorphismRecovery

/-!
# A common refinement of independent whole-family models

Two finitely presented models over the same coefficient ring which recover
the same original family have an actual common model at a finite enlargement.
Both comparison squares are Cartesian and both maps from the original
family remain the given maps. No faithful flatness of recovery is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Independently chosen Cartesian models admit a common finite coefficient refinement. -/
theorem exists_coefficient_common_model {A : Type u} [CommRing A]
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
    {X Y Z : Scheme.{u}} {r : X ⟶ Spec (.of A)}
    (p : Y ⟶ Spec (.of R)) (q : Z ⟶ Spec (.of R))
    [QuasiCompact p] [QuasiCompact q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    {a : X ⟶ Y} {b : X ⟶ Z}
    (hp : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hq : IsPullback b r q (Spec.map (CommRingCat.ofHom R.val.toRingHom))) :
    ∃ (S : Subalgebra ℤ A) (_ : Algebra.FiniteType ℤ S) (hRS : R ≤ S)
      (W : Scheme.{u}) (v : W ⟶ Spec (.of S)) (u : X ⟶ W)
      (c : W ⟶ Y) (d : W ⟶ Z),
      IsPullback c v p (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRS).toRingHom)) ∧
      IsPullback d v q (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRS).toRingHom)) ∧
      IsPullback u r v (Spec.map (CommRingCat.ofHom S.val.toRingHom)) ∧
      u ≫ c = a ∧ u ≫ d = b := by
  obtain ⟨i, f, hf, he⟩ := exists_coefficient_original_hom R p q hp hq (𝟙 X)
    (Category.id_comp r)
  let B := i.unop.val
  let _ : Algebra.FiniteType ℤ B := i.unop.property.2
  let bi := (coefficientSpectrumToInitial R).app i
  let pi := pullback.snd p bi
  let qi := pullback.snd q bi
  have hpi := coefficientModelRecovery_isPullback hp i
  have hqi := coefficientModelRecovery_isPullback hq i
  have : IsIso (immersionBaseChange pi qi f hf
      (Spec.map (CommRingCat.ofHom B.val.toRingHom))) :=
    cartesianMorphismRecovery_isIso hpi hqi (𝟙 X) f hf he (Category.id_comp r)
  obtain ⟨j, hj⟩ := exists_coefficient_isIso B pi qi f hf
  let bj := (coefficientSpectrumToInitial B).app j
  let fj := immersionBaseChange pi qi f hf bj
  let uj := coefficientModelRecovery hpi j
  let vj := pullback.snd pi bj
  let cj := pullback.fst pi bj ≫ pullback.fst p bi
  let dj := fj ≫ pullback.fst qi bj ≫ pullback.fst q bi
  have hbase : bj ≫ bi = Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (i.unop.property.1.trans j.unop.property.1)).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hc := (IsPullback.of_hasPullback pi bj).paste_horiz
    (IsPullback.of_hasPullback p bi)
  rw [hbase] at hc
  have hfj : IsPullback fj vj (pullback.snd qi bj) (𝟙 _) := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by simp only [fj, vj, immersionBaseChange_snd, Category.comp_id]⟩
  have hd := (hfj.paste_horiz (IsPullback.of_hasPullback qi bj)).paste_horiz
    (IsPullback.of_hasPullback q bi)
  simp only [Category.id_comp, hbase] at hd
  refine ⟨j.unop.val, j.unop.property.2,
    i.unop.property.1.trans j.unop.property.1, _, vj, uj, cj, dj, hc, ?_,
    coefficientModelRecovery_isPullback hpi j, ?_, ?_⟩
  · simpa only [dj, Category.assoc] using hd
  · dsimp only [uj, cj]
    rw [← Category.assoc, coefficientModelRecovery_fst, coefficientModelRecovery_fst]
  · change (coefficientModelRecovery hpi j ≫
        (immersionBaseChange pi qi f hf bj ≫ pullback.fst qi bj)) ≫
          pullback.fst q bi = b
    rw [immersionBaseChange_fst pi qi f hf bj, ← Category.assoc,
      coefficientModelRecovery_fst, ← he, Category.id_comp, coefficientModelRecovery_fst]

end FLT.Mazur.Approximation

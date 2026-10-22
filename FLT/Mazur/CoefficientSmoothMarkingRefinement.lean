/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientOriginalOpenDescent
public import FLT.Mazur.CoefficientSectionNeighborhood
public import FLT.Mazur.CoefficientSmoothOpenRefinement

/-!
# Refining a pointed model to retain smoothness at the marking

An original compact smooth neighborhood descends, becomes smooth at a
finite stage, and contains the entire refined marking after another finite
enlargement. The whole proper model and its original recovery are retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
open SectionCoverBaseChange
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The model can be refined until the original marking lies in its relative smooth locus. -/
theorem exists_coefficient_smooth_marking_refinement {A : Type u} [CommRing A]
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
    {X Y : Scheme.{u}} {r : X ⟶ Spec (.of A)} (p : Y ⟶ Spec (.of R))
    [IsProper p] [LocallyOfFinitePresentation p] {a : X ⟶ Y}
    (h : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (s : Spec (.of A) ⟶ X) (hs : s ≫ r = 𝟙 _)
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ p = 𝟙 _)
    (he : Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t = s ≫ a)
    (U : X.Opens) (hUc : IsCompact (U : Set X))
    (hUs : s ⁻¹ᵁ U = ⊤) [Smooth (U.ι ≫ r)] :
    ∃ (B : Subalgebra ℤ A) (_ : Algebra.FiniteType ℤ B) (hRB : R ≤ B)
      (Z : Scheme.{u}) (q : Z ⟶ Spec (.of B)) (f : X ⟶ Z) (c : Z ⟶ Y)
      (z : Spec (.of B) ⟶ Z),
      ∃ (_ : IsProper q) (_ : LocallyOfFinitePresentation q), z ≫ q = 𝟙 _ ∧
      IsPullback c q p (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRB).toRingHom)) ∧
      IsPullback f r q (Spec.map (CommRingCat.ofHom B.val.toRingHom)) ∧
      f ≫ c = a ∧ z ⁻¹ᵁ q.smoothLocus = ⊤ ∧
      Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫ z = s ≫ f := by
  obtain ⟨i, V, _, hV⟩ := exists_coefficient_original_open R p h U hUc
  let B₁ := i.unop.val
  let _ : Algebra.FiniteType ℤ B₁ := i.unop.property.2
  let bi := (coefficientSpectrumToInitial R).app i
  let pi := pullback.snd p bi
  let ai := coefficientModelRecovery h i
  have hi := coefficientModelRecovery_isPullback h i
  let ti := sectionMap p bi t ht
  have hti := sectionMap_snd p bi t ht
  have hei := coefficientSection_recovery h s hs t ht he i
  have : Smooth ((ai ⁻¹ᵁ V).ι ≫ r) := by
    change Smooth ((coefficientModelRecovery h i ⁻¹ᵁ V).ι ≫ r)
    rw [hV]
    infer_instance
  obtain ⟨j, hj⟩ := exists_coefficient_smooth_open B₁ pi hi V
  let B₂ := j.unop.val
  let _ : Algebra.FiniteType ℤ B₂ := j.unop.property.2
  let bj := (coefficientSpectrumToInitial B₁).app j
  let pj := pullback.snd pi bj
  let aj := coefficientModelRecovery hi j
  have hjp := coefficientModelRecovery_isPullback hi j
  let Vj := pullback.fst pi bj ⁻¹ᵁ V
  let tj := sectionMap pi bj ti hti
  have htj := sectionMap_snd pi bj ti hti
  have hej : Spec.map (CommRingCat.ofHom B₂.val.toRingHom) ≫ tj = s ≫ aj :=
    coefficientSection_recovery hi s hs ti hti hei j
  have hVj : aj ⁻¹ᵁ Vj = U := by
    change coefficientModelRecovery hi j ⁻¹ᵁ (pullback.fst pi bj ⁻¹ᵁ V) = U
    rw [← Scheme.Hom.comp_preimage, coefficientModelRecovery_fst]
    exact hV
  have hsj : (Spec.map (CommRingCat.ofHom B₂.val.toRingHom) ≫ tj) ⁻¹ᵁ Vj = ⊤ := by
    rw [hej, Scheme.Hom.comp_preimage, hVj, hUs]
  obtain ⟨k, hk⟩ := exists_coefficient_section_neighborhood B₂ pj tj htj Vj hsj
  let bk := (coefficientSpectrumToInitial B₂).app k
  let pk := pullback.snd pj bk
  let ak := coefficientModelRecovery hjp k
  let tk := sectionMap pj bk tj htj
  let Vk := pullback.fst pj bk ⁻¹ᵁ Vj
  have hVk := (isPullback_morphismRestrict (pullback.fst pj bk) Vj).paste_vert
    (IsPullback.of_hasPullback pj bk)
  have : Smooth (Vk.ι ≫ pk) := MorphismProperty.of_isPullback hVk hj
  have hRB := i.unop.property.1.trans (j.unop.property.1.trans k.unop.property.1)
  have hbase : (bk ≫ bj) ≫ bi =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRB).toRingHom) := by
    change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hc := ((IsPullback.of_hasPullback pj bk).paste_horiz
    (IsPullback.of_hasPullback pi bj)).paste_horiz (IsPullback.of_hasPullback p bi)
  rw [hbase] at hc
  refine ⟨k.unop.val, k.unop.property.2, hRB, _, pk, ak,
    (pullback.fst pj bk ≫ pullback.fst pi bj) ≫ pullback.fst p bi, tk,
    inferInstance, inferInstance, sectionMap_snd pj bk tj htj, hc,
    coefficientModelRecovery_isPullback hjp k, ?_, ?_, ?_⟩
  · change coefficientModelRecovery hjp k ≫
        ((pullback.fst pj bk ≫ pullback.fst pi bj) ≫ pullback.fst p bi) = a
    rw [← Category.assoc, ← Category.assoc, coefficientModelRecovery_fst,
      coefficientModelRecovery_fst, coefficientModelRecovery_fst]
  · exact section_smoothLocus_of_neighborhood pk tk Vk hk
  · exact coefficientSection_recovery hjp s hs tj htj hej k

end FLT.Mazur.Approximation

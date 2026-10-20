/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionSumRank

/-!
# Degree of Cartier section products in proper, possibly singular curves

The section-length argument only needs the section ideals themselves to be
relative Cartier. This gives the full constant-rank result for sections in a
smooth open even when the proper ambient family has singular fibers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

/-- Cartier section products have their actual number of factors as field length. -/
theorem divisorFieldLength_cartier_section_prod {k : Type} [Field k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) [IsProper f] {ι : Type*} (t : Finset ι)
    (s : ι → (Spec (.of k) ⟶ X)) (hs : ∀ i ∈ t, s i ≫ f = 𝟙 _)
    (hc : ∀ i ∈ t, RelativeEffectiveCartier f (s i).ker) :
    divisorFieldLength f (∏ i ∈ t, (s i).ker) = t.card := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.card_empty, divisorFieldLength_one]
  | @insert i t hi ih =>
    have hsi := hs i (Finset.mem_insert_self i t)
    have hst : ∀ j ∈ t, s j ≫ f = 𝟙 _ :=
      fun j hj ↦ hs j (Finset.mem_insert_of_mem hj)
    have hct : ∀ j ∈ t, RelativeEffectiveCartier f (s j).ker :=
      fun j hj ↦ hc j (Finset.mem_insert_of_mem hj)
    have hI := (hc i (Finset.mem_insert_self i t)).1
    have hJ := (relativeEffectiveCartier_prod f t (fun j ↦ (s j).ker) hct).1
    let _ : IsFinite ((s i).ker.subschemeι ≫ f) := by
      rw [← sectionImageIso_hom f (s i) hsi]
      infer_instance
    let _ := isFinite_section_prod f t s hst
    let _ : IsFinite (((s i).ker * ∏ j ∈ t, (s j).ker).subschemeι ≫ f) := by
      have he := Finset.prod_insert (f := fun j ↦ (s j).ker) hi
      exact (congrArg (fun J : X.IdealSheafData ↦ IsFinite (J.subschemeι ≫ f)) he).mp
        (isFinite_section_prod f (insert i t) s hs)
    rw [Finset.prod_insert hi, divisorFieldLength_mul f hI hJ,
      divisorFieldLength_section f (s i) hsi, ih hst hct, Finset.card_insert_of_notMem hi]
    omega

variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f]
  {ι : Type*} (t : Finset ι) (s : ι → (S ⟶ X)) (hs : ∀ i, s i ≫ f = 𝟙 S)
  (hc : ∀ i, RelativeEffectiveCartier f (s i).ker)

include hs hc in
/-- The full Cartier section product has the prescribed rank at every base point. -/
theorem finrank_cartier_section_prod (y : S) :
    ((∏ i ∈ t, (s i).ker).subschemeι ≫ f).finrank y = t.card := by
  let I : X.IdealSheafData := ∏ i ∈ t, (s i).ker
  let _ := isFinite_section_prod f t s (fun i _ ↦ hs i)
  let _ := (relativeEffectiveCartier_prod f t (fun i ↦ (s i).ker) (fun i _ ↦ hc i)).2
  let g := S.fromSpecResidueField y
  let z : Spec (S.residueField y) := IsLocalRing.closedPoint (S.residueField y)
  have hy : g z = y := S.fromSpecResidueField_apply y z
  rw [← hy, ← finrank_divisor_baseChange f g I z]
  let _ := isFinite_divisor_baseChange f g I
  rw [finrank_eq_finiteSchemeLength]
  change divisorFieldLength (pullback.snd f g) (I.comap (pullback.fst f g)) = _
  rw [section_prod_comap_eq f g t s hs]
  apply divisorFieldLength_cartier_section_prod
  · intro i _
    exact sectionBaseChange_snd f g (s i) (hs i)
  · intro i _
    rw [ker_sectionBaseChange]
    exact relativeCartierBaseChange f g _ (hc i)

include hs hc in
/-- A full product of Cartier section ideals is finite locally free of its number of factors. -/
theorem finiteLocallyFreeDegree_cartier_section_prod [LocallyOfFinitePresentation f] :
    FiniteLocallyFreeDegree ((∏ i ∈ t, (s i).ker).subschemeι ≫ f) t.card := by
  have h := relativeEffectiveCartier_prod f t (fun i ↦ (s i).ker) (fun i _ ↦ hc i)
  exact ⟨isFinite_section_prod f t s (fun i _ ↦ hs i), h.2,
    h.1.locallyOfFinitePresentation_comp f, finrank_cartier_section_prod f t s hs hc⟩

/-- Smooth-open sections give the full degree even when the proper ambient curve is singular. -/
theorem finiteLocallyFreeDegree_smoothOpen_section_prod {U : Scheme}
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f)]
    [LocallyOfFinitePresentation f] (a : ι → (S ⟶ U))
    (ha : ∀ i, a i ≫ j ≫ f = 𝟙 S) :
    FiniteLocallyFreeDegree ((∏ i ∈ t, (a i ≫ j).ker).subschemeι ≫ f) t.card := by
  apply finiteLocallyFreeDegree_cartier_section_prod f t (fun i ↦ a i ≫ j)
  · intro i
    simpa only [Category.assoc] using ha i
  · intro i
    exact smoothOpenSectionCartier j f (a i) inferInstance inferInstance inferInstance (ha i)

end FLT.Mazur.FCurve

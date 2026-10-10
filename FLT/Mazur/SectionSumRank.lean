/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionSumFieldLength
public import FLT.Mazur.DivisorBaseChangeRank
public import FLT.Mazur.CartierImmersionFinitePresentation

/-!
# Constant rank of sums of sections

At each base point, the actual ideal pulls back to a product of rational section
ideals over the residue field. Their scheme lengths add, counting collisions.
The finite flat rank is therefore the number of factors on every base component.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
  {ι : Type*} (t : Finset ι) (s : ι → (S ⟶ X)) (hs : ∀ i, s i ≫ f = 𝟙 S)

include hs in
/-- A product of section ideals has rank its number of factors at every base point. -/
theorem finrank_section_prod (y : S) :
    ((∏ i ∈ t, (s i).ker).subschemeι ≫ f).finrank y = t.card := by
  let I : X.IdealSheafData := ∏ i ∈ t, (s i).ker
  let _ := isFinite_section_prod f t s (fun i _ ↦ hs i)
  let _ := (relativeEffectiveCartier_section_prod f t s (fun i _ ↦ hs i)).2
  let g := S.fromSpecResidueField y
  let z : Spec (S.residueField y) := IsLocalRing.closedPoint (S.residueField y)
  have hy : g z = y := S.fromSpecResidueField_apply y z
  rw [← hy, ← finrank_divisor_baseChange f g I z]
  let _ := isFinite_divisor_baseChange f g I
  rw [finrank_eq_finiteSchemeLength]
  change divisorFieldLength (pullback.snd f g) (I.comap (pullback.fst f g)) = _
  rw [section_prod_comap_eq f g t s hs]
  let _ : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f g inferInstance
  exact divisorFieldLength_section_prod (pullback.snd f g) t
    (fun i ↦ sectionBaseChange f g (s i) (hs i))
    (fun i _ ↦ sectionBaseChange_snd f g (s i) (hs i))

include hs in
/-- The section product satisfies the finite locally free constant-degree contract. -/
theorem finiteLocallyFreeDegree_section_prod :
    FiniteLocallyFreeDegree ((∏ i ∈ t, (s i).ker).subschemeι ≫ f) t.card := by
  let _ := SmoothOfRelativeDimension.smooth 1 f
  have hc := relativeEffectiveCartier_section_prod f t s (fun i _ ↦ hs i)
  exact ⟨isFinite_section_prod f t s (fun i _ ↦ hs i), hc.2,
    hc.1.locallyOfFinitePresentation_comp f, finrank_section_prod f t s hs⟩

end FLT.Mazur.FCurve

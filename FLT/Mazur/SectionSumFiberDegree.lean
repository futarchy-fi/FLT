/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionSumFieldLength
public import FLT.Mazur.DivisorBaseChangeRank

/-!
# Cohomological degree on every field fiber of a section sum

Arbitrary field-valued base maps recover actual products of rational section
ideals. Both the scheme length and the cohomological degree of their positive
divisor lines equal the number of factors, including repeated sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
  {ι : Type*} (t : Finset ι) (s : ι → (S ⟶ X)) (hs : ∀ i, s i ≫ f = 𝟙 S)
  {k : Type} [Field k] (g : Spec (CommRingCat.of k) ⟶ S)

include hs in
/-- Every field fiber has its prescribed actual length, without any splitting-field choice. -/
theorem section_prod_fieldFiber_length :
    divisorFieldLength (pullback.snd f g)
      ((∏ i ∈ t, (s i).ker).comap (pullback.fst f g)) = t.card := by
  rw [section_prod_comap_eq f g t s hs]
  let _ : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f g inferInstance
  exact divisorFieldLength_section_prod (pullback.snd f g) t
    (fun i ↦ sectionBaseChange f g (s i) (hs i))
    (fun i _ ↦ sectionBaseChange_snd f g (s i) (hs i))

/-- The positive divisor line on every field fiber has actual cohomological degree `card t`. -/
theorem section_prod_fieldFiber_degree :
    curveSheafDegree (pullback.snd f g)
      (divisorLineBundle ((∏ i ∈ t, (s i).ker).comap (pullback.fst f g))
        (relativeCartierBaseChange f g _
          (relativeEffectiveCartier_section_prod f t s (fun i _ ↦ hs i))).1) =
      (t.card : ℤ) := by
  let _ := isFinite_section_prod f t s (fun i _ ↦ hs i)
  let _ := isFinite_divisor_baseChange f g (∏ i ∈ t, (s i).ker)
  rw [divisor_degree_eq_fieldLength, section_prod_fieldFiber_length f t s hs g]

end FLT.Mazur.FCurve

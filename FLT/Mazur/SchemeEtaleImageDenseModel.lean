/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeDenseOpenComparison
public import FLT.Mazur.SchemeEtaleImageQuotient
public import FLT.Mazur.SchemeFppfTargetOpen

/-!
# Effective regions of schematically dense coefficient enlargements

Descent along an etale full-kernel quotient constructs an open comparison
into a schematically dense model. The complete new projection is etale,
and its actual fppf region is the inverse image of the old coefficient image.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeEtaleImageDenseModel
set_option backward.isDefEq.respectTransparency false
variable {E A T J : Scheme} {p q : E ⟶ A} (w : A ⟶ T) [Etale w]
  (H : IsPullback p q w w) (j : A ⟶ J) (hj : p ≫ j = q ≫ j)
  (r : J ⟶ T) (hr : j ≫ r = w)
local notation "U" => SchemeEtaleImageQuotient.image w
local notation "e" => SchemeEtaleImageQuotient.projection w

/-- The old actual quotient maps to the new coefficient scheme by full-kernel descent. -/
def comparison : (U).toScheme ⟶ J := SchemeEtaleImageQuotient.descend w H j hj

@[reassoc]
theorem projection_comparison : e ≫ comparison w H j hj = j :=
  SchemeEtaleImageQuotient.projection_descend w H j hj

include hr in
@[reassoc]
theorem comparison_toOld : comparison w H j hj ≫ r = (U).ι :=
  SchemeEtaleImageQuotient.descend_comp w H j hj r hr

/-- Surjectivity of the old quotient identifies the comparison's actual source image. -/
theorem range_comparison : Set.range (comparison w H j hj) = Set.range j := by
  have he : Set.range e = Set.univ :=
    Set.range_eq_univ.mpr (SchemeEtaleImageQuotient.projection_surjective w).1
  conv_rhs => rw [← projection_comparison w H j hj]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, he, Set.image_univ]

variable [IsSchemeTheoreticallyDominant j] [QuasiCompact j] [IsSeparated r]

include hr in
/-- The comparison is an open immersion, with the full scheme structure retained. -/
theorem comparison_isOpenImmersion : IsOpenImmersion (comparison w H j hj) :=
  SchemeDenseOpenComparison.isOpenImmersion j e (comparison w H j hj) r (U).ι
    (projection_comparison w H j hj) (comparison_toOld w H j hj r hr)

include H hj hr in
/-- The complete new projection is etale, not only its generic or reduced restriction. -/
theorem projection_etale : Etale j := by
  let _ := comparison_isOpenImmersion w H j hj r hr
  rw [← projection_comparison w H j hj]
  infer_instance

/-- The new scheme over the old actual image is isomorphic to that old quotient. -/
def comparisonIso : (U).toScheme ≅ pullback r (U).ι := by
  let hs := comparison_toOld w H j hj r hr
  let _ := SchemeDenseOpenComparison.lift_isIso j e (comparison w H j hj) r (U).ι
    (projection_comparison w H j hj) hs
  exact asIso (SchemeDenseOpenComparison.lift (comparison w H j hj) r (U).ι hs)

@[reassoc]
theorem comparisonIso_fst : (comparisonIso w H j hj r hr).hom ≫ pullback.fst r (U).ι =
    comparison w H j hj :=
  SchemeDenseOpenComparison.lift_fst _ _ _ (comparison_toOld w H j hj r hr)

@[reassoc]
theorem comparisonIso_snd : (comparisonIso w H j hj r hr).hom ≫ pullback.snd r (U).ι =
    𝟙 (U).toScheme :=
  SchemeDenseOpenComparison.lift_snd _ _ _ (comparison_toOld w H j hj r hr)

include H hj hr in
/-- The actual image of the new projection is exactly the inverse image of the old open. -/
theorem range_projection : Set.range j = r ⁻¹' (U : Set T) := by
  have he : Set.range (comparisonIso w H j hj r hr).hom = Set.univ :=
    Set.range_eq_univ.mpr (comparisonIso w H j hj r hr).hom.homeomorph.surjective
  rw [← range_comparison w H j hj, ← comparisonIso_fst w H j hj r hr,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, he,
    Set.image_univ, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

include H hj hr in
/-- The maximal effective fppf region has exactly this scheme-theoretically justified support. -/
theorem fppfLocus_eq_preimage
    [LocallyOfFinitePresentation j] :
    (SchemeFppfTargetOpen.locus j : Set J) = r ⁻¹' (U : Set T) := by
  let _ := projection_etale w H j hj r hr
  rw [SchemeFppfTargetOpen.coe_locus, SchemeFlatTargetOpen.locus_top]
  simpa using range_projection w H j hj r hr

variable [LocallyOfFinitePresentation j]

/-- The actual maximal fppf open of the new model is the constructed old quotient scheme. -/
def effectiveIso : (U).toScheme ≅ (SchemeFppfTargetOpen.locus j).toScheme := by
  let _ := comparison_isOpenImmersion w H j hj r hr
  exact IsOpenImmersion.isoOfRangeEq (comparison w H j hj)
    (SchemeFppfTargetOpen.locus j).ι (by
      rw [Scheme.Opens.range_ι, range_comparison w H j hj,
        fppfLocus_eq_preimage w H j hj r hr, range_projection w H j hj r hr])

/-- The isomorphism retains the actual map into the joint coefficient scheme. -/
@[reassoc]
theorem effectiveIso_ι : (effectiveIso w H j hj r hr).hom ≫
    (SchemeFppfTargetOpen.locus j).ι = comparison w H j hj := by
  unfold effectiveIso
  exact IsOpenImmersion.lift_fac _ _ _

/-- The old coefficient morphism is retained by the actual effective-region isomorphism. -/
@[reassoc]
theorem effectiveIso_toOld : (effectiveIso w H j hj r hr).hom ≫
    (SchemeFppfTargetOpen.locus j).ι ≫ r = (U).ι := by
  rw [effectiveIso_ι_assoc, comparison_toOld w H j hj r hr]

end FLT.Mazur.SchemeEtaleImageDenseModel

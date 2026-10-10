/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertPairTransitions
public import FLT.Mazur.HilbertSupportOpenPullback

/-!
# Triple Hilbert intersections as categorical pullbacks

Support in the full common triple ambient open represents the actual
pullback of pairwise open chart inclusions. Both projections are identified
with actual support inclusions, preparing the gluing rotation maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ)

/-- Support intersections are actual pullbacks over the full affine Hilbert chart. -/
theorem supportIntersection_isPullback (i : A.Index) (U V : Z.Opens) :
    IsPullback (A.inclusion d i (inf_le_left : U ⊓ V ≤ U))
      (A.inclusion d i (inf_le_right : U ⊓ V ≤ V))
      (A.support d i U).ι (A.support d i V).ι := by
  refine (isPullback_opens_inf (A.support d i U) (A.support d i V)).of_iso
    ((A.hilbert d i).isoOfEq (A.support_inf d i U V).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Scheme.isoOfEq_hom,
      inclusion, openAmbientHilbertInclusion, Scheme.homOfLE_homOfLE]
  · simp only [Iso.refl_hom, Category.comp_id, Scheme.isoOfEq_hom,
      inclusion, openAmbientHilbertInclusion, Scheme.homOfLE_homOfLE]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The full common triple open, viewed from the first chart. -/
def triple (i j k : A.Index) : Z.Opens := A.common i j ⊓ A.common i k

/-- The triple open is contained in its first original chart. -/
theorem triple_le_first (i j k : A.Index) : A.triple i j k ≤ (A.chart i).opensRange :=
  inf_le_left.trans inf_le_left

/-- The triple open is contained in its second original chart. -/
theorem triple_le_second (i j k : A.Index) : A.triple i j k ≤ (A.chart j).opensRange :=
  inf_le_left.trans inf_le_right

/-- The triple open is contained in its third original chart. -/
theorem triple_le_third (i j k : A.Index) : A.triple i j k ≤ (A.chart k).opensRange :=
  inf_le_right.trans inf_le_right

/-- The triple open lies in the opposite pairwise overlap. -/
theorem triple_le_opposite (i j k : A.Index) : A.triple i j k ≤ A.common j k :=
  le_inf (A.triple_le_second i j k) (A.triple_le_third i j k)

/-- The common-triple Hilbert scheme is the actual pairwise-inclusion pullback. -/
def triplePullbackIso (i j k : A.Index) :
    (A.support d i (A.triple i j k)).toScheme ≅
      pullback (A.overlap d i j).ι (A.overlap d i k).ι :=
  (A.supportIntersection_isPullback d i (A.common i j) (A.common i k)).isoPullback

/-- The first pullback projection is the full triple-to-pair support inclusion. -/
@[reassoc (attr := simp)]
theorem triplePullbackIso_fst (i j k : A.Index) :
    (A.triplePullbackIso d i j k).hom ≫ pullback.fst _ _ =
      A.inclusion d i (inf_le_left : A.triple i j k ≤ A.common i j) :=
  IsPullback.isoPullback_hom_fst _

/-- The second pullback projection is the full triple-to-pair support inclusion. -/
@[reassoc (attr := simp)]
theorem triplePullbackIso_snd (i j k : A.Index) :
    (A.triplePullbackIso d i j k).hom ≫ pullback.snd _ _ =
      A.inclusion d i (inf_le_right : A.triple i j k ≤ A.common i k) :=
  IsPullback.isoPullback_hom_snd _

end FLT.Mazur.HilbertChart.AmbientQuotientCharts

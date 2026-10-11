/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurveDivisorPullback

/-!
# Specializing ordered divisors on the original curve

A section of the ordered parameter space induces an actual cartesian map from
the original curve. The universal divisor pulls back to the full product of
the corresponding section ideals on that original curve.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.OrderedCurvePower
variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
  (a : S ⟶ space f n) (ha : a ≫ base f n = 𝟙 S)

/-- Specialization from the unchanged original curve to the universal curve. -/
def sectionCurveMap : X ⟶ curve f n :=
  pullback.lift (𝟙 X) (f ≫ a) (by simp [ha])

@[reassoc (attr := simp)]
lemma sectionCurveMap_fst : sectionCurveMap f n a ha ≫ pullback.fst f (base f n) = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sectionCurveMap_snd : sectionCurveMap f n a ha ≫ projection f n = f ≫ a :=
  pullback.lift_snd _ _ _

/-- The original curve, not a replacement total space, is the parameter fiber. -/
theorem sectionCurveMap_isPullback :
    IsPullback (sectionCurveMap f n a ha) f (projection f n) a := by
  apply IsPullback.of_right (h₁₂ := pullback.fst f (base f n)) (h₂₂ := base f n)
    (v₁₃ := f) ?_ (by simp) (IsPullback.of_hasPullback f (base f n))
  simp only [sectionCurveMap_fst, ha]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The graph specializes to the original section, in a cartesian square. -/
theorem sectionGraph_isPullback (i : Fin n) :
    IsPullback (a ≫ point f n i) a (sectionCurveMap f n a ha) (graph f n i) := by
  have hw : (a ≫ point f n i) ≫ sectionCurveMap f n a ha = a ≫ graph f n i := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, sectionCurveMap_snd, graph_projection,
        Category.comp_id, point_base_assoc]
      rw [← Category.assoc, ha, Category.id_comp]
  apply IsPullback.of_right (h₁₂ := f) (h₂₂ := projection f n)
    (v₁₃ := a) ?_ hw (sectionCurveMap_isPullback f n a ha).flip
  simp only [Category.assoc, point_base, ha, graph_projection]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Specialization identifies the full graph kernel with the original section kernel. -/
theorem sectionGraph_ker_comap [IsSeparated f] (i : Fin n) :
    (graph f n i).ker.comap (sectionCurveMap f n a ha) = (a ≫ point f n i).ker := by
  let _ := FCurve.isClosedImmersion_section (projection f n) (graph f n i)
    (graph_projection f n i)
  let H := sectionGraph_isPullback f n a ha i
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

/-- The full universal ideal specializes to the full original section-ideal product. -/
theorem divisorIdeal_section_comap [IsSeparated f] :
    (divisorIdeal f n).comap (sectionCurveMap f n a ha) =
      ∏ i, (a ≫ point f n i).ker := by
  simp only [divisorIdeal, FCurve.idealSheaf_comap_prod, sectionGraph_ker_comap]

end FLT.Mazur.OrderedCurvePower

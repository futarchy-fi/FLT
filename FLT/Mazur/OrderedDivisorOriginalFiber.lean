/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurveDivisorPullback

/-!
# Ordered divisor specialization on an independently specified fiber

An ordered tuple of sections on any cartesian fiber defines a parameter in
the original curve's ordered power. The full universal ideal pulls back to
the original fiber's section-ideal product, without replacing its total space.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.OrderedCurvePower
variable {C X T S : Scheme.{u}} {c : C ⟶ X} {q : C ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (H : IsPullback c q f g) (d : ℕ) (p : Fin d → (T ⟶ C))
  (hp : ∀ i, p i ≫ q = 𝟙 T)

/-- The tuple on the given fiber determines a point of the original ordered parameter space. -/
def fiberParameter : T ⟶ space f d :=
  classify f d g (fun i ↦ p i ≫ c) (fun i ↦ by
    rw [Category.assoc, H.w, ← Category.assoc, hp i, Category.id_comp])

@[reassoc (attr := simp)]
lemma fiberParameter_point (i : Fin d) :
    fiberParameter H d p hp ≫ point f d i = p i ≫ c := by simp [fiberParameter]

@[reassoc (attr := simp)]
lemma fiberParameter_base : fiberParameter H d p hp ≫ base f d = g := by
  simp [fiberParameter]

/-- The map from the given original fiber to the original universal curve. -/
def fiberCurveMap : C ⟶ curve f d :=
  pullback.lift c (q ≫ fiberParameter H d p hp) (by simp [H.w])

@[reassoc (attr := simp)]
lemma fiberCurveMap_fst : fiberCurveMap H d p hp ≫ pullback.fst f (base f d) = c :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma fiberCurveMap_snd :
    fiberCurveMap H d p hp ≫ projection f d = q ≫ fiberParameter H d p hp :=
  pullback.lift_snd _ _ _

/-- The supplied original total space is the actual fiber of the universal family. -/
theorem fiberCurveMap_isPullback :
    IsPullback (fiberCurveMap H d p hp) q (projection f d) (fiberParameter H d p hp) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst f (base f d)) (h₂₂ := base f d)
    (v₁₃ := f) ?_ (by simp) (IsPullback.of_hasPullback f (base f d))
  simpa only [fiberCurveMap_fst, fiberParameter_base] using H

/-- Each universal graph has the supplied original section as its cartesian fiber. -/
theorem fiberGraph_isPullback (i : Fin d) :
    IsPullback (p i) (fiberParameter H d p hp) (fiberCurveMap H d p hp) (graph f d i) := by
  have hw : p i ≫ fiberCurveMap H d p hp = fiberParameter H d p hp ≫ graph f d i := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, fiberCurveMap_snd, graph_projection, Category.comp_id]
      rw [← Category.assoc, hp i, Category.id_comp]
  apply IsPullback.of_right (h₁₂ := q) (h₂₂ := projection f d)
    (v₁₃ := fiberParameter H d p hp) ?_ hw (fiberCurveMap_isPullback H d p hp).flip
  simp only [hp i, graph_projection]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The universal graph kernel pulls back to the supplied original section's full kernel. -/
theorem fiberGraph_ker_comap [IsSeparated f] (i : Fin d) :
    (graph f d i).ker.comap (fiberCurveMap H d p hp) = (p i).ker := by
  let _ := FCurve.isClosedImmersion_section (projection f d) (graph f d i)
    (graph_projection f d i)
  let E := fiberGraph_isPullback H d p hp i
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso E.isoPullback.hom, E.isoPullback_hom_fst]

/-- All original fiber multiplicities are retained in the specialized universal ideal. -/
theorem divisorIdeal_fiber_comap [IsSeparated f] :
    (divisorIdeal f d).comap (fiberCurveMap H d p hp) = ∏ i, (p i).ker := by
  simp only [divisorIdeal, FCurve.idealSheaf_comap_prod, fiberGraph_ker_comap]

end FLT.Mazur.OrderedCurvePower

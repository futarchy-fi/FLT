/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSupportOpenLattice

/-!
# Actual pullbacks of Hilbert support inclusions

The representative of simultaneous support in two ambient opens is the
scheme-theoretic pullback of their inclusions, even inside a larger support
open. This identifies the triple intersections needed for Hilbert gluing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

variable (R I : Type u) [CommRing R] (d : ℕ) (K : Ideal (MvPolynomial I R))
variable (U V W : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)

/-- Simultaneous support gives the actual pullback over a larger support open. -/
theorem openAmbientHilbertInclusion_isPullback (hU : U ≤ W) (hV : V ≤ W) :
    IsPullback (openAmbientHilbertInclusion R I d K (U ⊓ V) U inf_le_left)
      (openAmbientHilbertInclusion R I d K (U ⊓ V) V inf_le_right)
      (openAmbientHilbertInclusion R I d K U W hU)
      (openAmbientHilbertInclusion R I d K V W hV) := by
  unfold openAmbientHilbertInclusion
  refine (isPullback_opens_inf_le
    (ambientHilbertSupportOpen_mono R I d K U W hU)
    (ambientHilbertSupportOpen_mono R I d K V W hV)).of_iso
    ((ambientHilbertScheme R I d K).isoOfEq
      (ambientHilbertSupportOpen_inf R I d K U V).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Scheme.isoOfEq_hom,
      Scheme.homOfLE_homOfLE]
  · simp only [Iso.refl_hom, Category.comp_id, Scheme.isoOfEq_hom,
      Scheme.homOfLE_homOfLE]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The canonical comparison with the categorical pullback of Hilbert inclusions. -/
def openAmbientHilbertIntersectionIso (hU : U ≤ W) (hV : V ≤ W) :
    (ambientHilbertSupportOpen R I d K (U ⊓ V)).toScheme ≅
      pullback (openAmbientHilbertInclusion R I d K U W hU)
        (openAmbientHilbertInclusion R I d K V W hV) :=
  (openAmbientHilbertInclusion_isPullback R I d K U V W hU hV).isoPullback

/-- The first projection is the actual support inclusion. -/
@[reassoc]
theorem openAmbientHilbertIntersectionIso_fst (hU : U ≤ W) (hV : V ≤ W) :
    (openAmbientHilbertIntersectionIso R I d K U V W hU hV).hom ≫ pullback.fst _ _ =
      openAmbientHilbertInclusion R I d K (U ⊓ V) U inf_le_left :=
  IsPullback.isoPullback_hom_fst _

/-- The second projection is the actual support inclusion. -/
@[reassoc]
theorem openAmbientHilbertIntersectionIso_snd (hU : U ≤ W) (hV : V ≤ W) :
    (openAmbientHilbertIntersectionIso R I d K U V W hU hV).hom ≫ pullback.snd _ _ =
      openAmbientHilbertInclusion R I d K (U ⊓ V) V inf_le_right :=
  IsPullback.isoPullback_hom_snd _

end FLT.Mazur.HilbertChart

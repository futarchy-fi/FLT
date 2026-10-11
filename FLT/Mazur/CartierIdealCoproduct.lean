/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedIdealCoverGluing
public import FLT.Mazur.CartierCharts
public import Mathlib.AlgebraicGeometry.Cover.Sigma

/-!
# Full Cartier ideals on a coproduct of schemes

Actual closed-family open gluing assembles arbitrary component ideals. Their
full comaps are recovered, and the Cartier condition follows on the open cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {ι : Type u} (Y : ι → Scheme.{u}) (I : ∀ i, (Y i).IdealSheafData)

/-- On an empty scheme every full ideal is the unit ideal. -/
lemma idealSheaf_eq_top_of_isEmpty {T : Scheme.{u}} [IsEmpty T] (J : T.IdealSheafData) :
    J = ⊤ :=
  J.support_eq_bot_iff.mp (SetLike.ext fun x ↦ isEmptyElim x)

/-- Component ideals match on the disjoint-union open cover. -/
lemma coproductIdeals_match (i j : ι) :
    (I i).comap (pullback.fst (Sigma.ι Y i) (Sigma.ι Y j)) =
      (I j).comap (pullback.snd (Sigma.ι Y i) (Sigma.ι Y j)) := by
  classical
  by_cases hij : i = j
  · subst j
    congr 1
    exact (cancel_mono (Sigma.ι Y i)).mp pullback.condition
  · let _ := isEmpty_pullback_sigmaι_of_ne Y hij
    exact (idealSheaf_eq_top_of_isEmpty _).trans (idealSheaf_eq_top_of_isEmpty _).symm

/-- The actual ideal on the coproduct obtained by gluing the closed component subschemes. -/
def coproductIdeal : (∐ Y).IdealSheafData :=
  (ClosedIdealCover.toBase (sigmaOpenCover Y) I (coproductIdeals_match Y I)).ker

/-- Restriction recovers each full component ideal exactly. -/
@[simp]
lemma coproductIdeal_comap (i : ι) : (coproductIdeal Y I).comap (Sigma.ι Y i) = I i :=
  ClosedIdealCover.ker_toBase_comap (sigmaOpenCover Y) I (coproductIdeals_match Y I) i

/-- Cartier component ideals assemble to a Cartier ideal on the actual coproduct. -/
theorem coproductIdeal_cartier (hI : ∀ i, EffectiveCartier (I i)) :
    EffectiveCartier (coproductIdeal Y I) := by
  apply (effectiveCartier_iff_openCover _ (sigmaOpenCover Y)).mpr
  intro i
  simpa only [sigmaOpenCover_f, coproductIdeal_comap] using hI i

end FLT.Mazur.FCurve

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertUniversalIntersection
public import FLT.Mazur.AmbientHilbertUniversalPairCompatibility
public import FLT.Mazur.ClosedIdealAffineCoverDescent
public import FLT.Mazur.IdealSheafOpenCoverDetection

/-!
# Descent of the full universal Hilbert ideal

The explicit pair compatibility is transferred to the actual ambient cover
intersections. Effective ideal descent constructs the full global ideal,
with its chart restrictions and uniqueness, including nonreduced structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]

/-- Full universal ideals agree on the actual categorical ambient chart intersection. -/
theorem chartUniversalIdeal_compatible (i j : A.Index) :
    (A.chartUniversalFamily d i).val.comap
        (pullback.fst (A.universalAmbientChart d i) (A.universalAmbientChart d j)) =
      (A.chartUniversalFamily d j).val.comap
        (pullback.snd (A.universalAmbientChart d i) (A.universalAmbientChart d j)) := by
  have h := congrArg Subtype.val (A.chartUniversalFamily_pair d i j)
  change (A.chartUniversalFamily d j).val.comap (A.universalAmbientOverlapSnd d i j) =
    (A.chartUniversalFamily d i).val.comap (A.universalAmbientOverlapFst d i j) at h
  have hp := A.universalAmbientOverlap_isPullback d i j
  rw [← hp.isoPullback_inv_fst, ← hp.isoPullback_inv_snd, comap_comp, comap_comp, h]

/-- The constructed full chart ideals form compatible data on the actual ambient cover. -/
def universalCompatibleIdeals : CompatibleIdeals (A.universalAmbientCover d) :=
  ⟨fun i ↦ (A.chartUniversalFamily d i).val, A.chartUniversalIdeal_compatible d⟩

/-- The global full universal ideal in the original ambient over the glued Hilbert scheme. -/
def universalIdeal : (pullback (A.gluedBase d) z).IdealSheafData :=
  descendIdeal (A.universalAmbientCover d) (A.universalCompatibleIdeals d)

/-- Restricting the global universal ideal recovers the complete universal chart family. -/
theorem universalIdeal_restrict (i : A.Index) :
    (A.universalIdeal d).comap (A.universalAmbientChart d i) =
      (A.chartUniversalFamily d i).val :=
  descendIdeal_restrict (A.universalAmbientCover d) (A.universalCompatibleIdeals d) i

/-- The full global ideal is uniquely determined by its actual universal chart restrictions. -/
theorem universalIdeal_unique (J : (pullback (A.gluedBase d) z).IdealSheafData)
    (hJ : ∀ i, J.comap (A.universalAmbientChart d i) = (A.chartUniversalFamily d i).val) :
    J = A.universalIdeal d := by
  apply BaseAdicThickening.idealSheaf_ext_of_openCover (A.universalAmbientCover d)
  intro i
  exact (hJ i).trans (A.universalIdeal_restrict d i).symm

end FLT.Mazur.HilbertChart.AmbientQuotientCharts

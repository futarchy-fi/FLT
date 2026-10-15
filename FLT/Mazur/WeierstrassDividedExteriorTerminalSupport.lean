/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOppositeBoundarySupport

/-!
# The preceding exterior meets the new divided chart only away from π

Any such intersection passes through both opposite boundaries of the newest
successive chart. The original incidence equation makes π invertible there.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {k : ℕ} {d : Data W π k} (E : Exterior d)
  (e : Data W π (k + 1))
local notation "F" => E.advance hπ e

/-- A terminal intersection forces a point into both original opposite boundaries. -/
theorem Exterior.retained_divided_intersection_lift (a : E.carrier) (c : chart e)
    (h : (E.retained hπ e ≫ (F).exteriorChart) a = (F).dividedChart c) :
    ∃ b : boundary e, (F).attach b = E.retained hπ e a ∧ boundaryInclusion e b = c ∧
      nextToX e b ∈ Set.range (previousToX hπ d e) := by
  obtain ⟨b, hb, hc⟩ := (SchemeOpenPushout.inl_eq_inr_iff
    (F).attach (boundaryInclusion e) (E.retained hπ e a) c).mp h
  refine ⟨b, hb, hc, ?_⟩
  rw [← E.newX_retained_preimage hπ e]
  exact ⟨a, hb.symm⟩

variable (base : (E.advance hπ e).whole ⟶ Spec (.of R))
  (hbase : E.newX hπ e ≫ (E.advance hπ e).exteriorChart ≫ base =
    Spec.map (CommRingCat.ofHom (algebraMap R
      (WeierstrassSuccessiveX.Coordinate W (π ^ k) π e.b3 e.b4 e.b6))))

include hbase in
/-- The entire preceding exterior misses the special part of the terminal divided chart. -/
theorem Exterior.retained_divided_parameter_notMem (a : E.carrier) (c : chart e)
    (h : (E.retained hπ e ≫ (F).exteriorChart) a = (F).dividedChart c) :
    π ∉ (base ((F).dividedChart c)).asIdeal := by
  obtain ⟨b, hb, hc, hp⟩ := E.retained_divided_intersection_lift hπ e a c h
  have hn := oppositeBoundary_parameter_notMem hπ d e (nextToX e b) ⟨b, rfl⟩ hp
  have hm : (E.newX hπ e ≫ (F).exteriorChart ≫ base) (nextToX e b) =
      base ((F).dividedChart c) := by
    change base ((F).exteriorChart ((F).attach b)) = _
    rw [hb]
    exact congrArg base h
  rw [hbase] at hm
  rw [← hm]
  exact hn

end FLT.Mazur.WeierstrassDividedDepth

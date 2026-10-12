/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleHilbertCommonAmbientChart
public import FLT.Mazur.AmpleFiniteAffineNeighborhood

/-!
# Common ambient charts refine full-support intersections

The full universal support locus preserves intersections. Within any such
locus, finitely many Hilbert points have a common original affine ambient
chart contained in the prescribed ambient open. Thus common chart choices
can be refined without discarding any of the specified full fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.FCurve
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {Z : Scheme} (z : Z ⟶ Spec (.of R)) [IsProper z]
  (d : ℕ)
local notation "A" => allAffineAmbientCharts z

/-- The full universal family's support locus in an arbitrary original ambient open. -/
def universalAmbientSupport (W : Z.Opens) : ((A).gluedHilbert d).Opens :=
  relativeIdealFamilySupportOpen z d ((A).gluedBase d) ((A).universalFamily d) W

/-- Membership retains every point of the full fiber, with its actual residue extensions. -/
theorem mem_universalAmbientSupport (W : Z.Opens) (x : (A).gluedHilbert d) :
    x ∈ universalAmbientSupport z d W ↔
      relativeIdealFiberSupport z d ((A).gluedBase d) ((A).universalFamily d) x ⊆ W :=
  (mem_relativeIdealFamilySupportOpen _ _ _ _ _ _).trans
    (relativeIdealFiberSupport_subset_iff _ _ _ _ _ _).symm

/-- Original ambient inclusion gives actual inclusion of full universal support loci. -/
theorem universalAmbientSupport_mono {W T : Z.Opens} (h : W ≤ T) :
    universalAmbientSupport z d W ≤ universalAmbientSupport z d T := by
  intro x hx
  exact (mem_universalAmbientSupport z d T x).mpr
    (((mem_universalAmbientSupport z d W x).mp hx).trans h)

/-- Full universal support in an intersection is precisely simultaneous support. -/
theorem universalAmbientSupport_inf (W T : Z.Opens) :
    universalAmbientSupport z d (W ⊓ T) =
      universalAmbientSupport z d W ⊓ universalAmbientSupport z d T := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  change x ∈ universalAmbientSupport z d (W ⊓ T) ↔
    x ∈ universalAmbientSupport z d W ∧ x ∈ universalAmbientSupport z d T
  rw [mem_universalAmbientSupport, mem_universalAmbientSupport, mem_universalAmbientSupport]
  exact Set.subset_inter_iff

/-- For an original affine ambient, the full support locus is its actual Hilbert chart image. -/
theorem universalAmbientSupport_affine (U : Z.affineOpens) :
    universalAmbientSupport z d U.val = ((A).hilbertChart d U).opensRange := by
  have h := (A).chartSupportLocus_eq d U
  unfold AmbientQuotientCharts.chartSupportLocus at h
  rw [allAffineAmbientCharts_opensRange] at h
  exact h

variable {L : Z.Modules} (hL : AmpleLineBundle L)

include hL in
/-- Finitely many full fibers in an ambient open have one affine ambient refinement inside it. -/
theorem exists_common_ambient_refinement (W : Z.Opens) (t : Set ((A).gluedHilbert d))
    (ht : t.Finite) (htW : t ⊆ universalAmbientSupport z d W) :
    ∃ U : Z.affineOpens, U.val ≤ W ∧ t ⊆ ((A).hilbertChart d U).opensRange := by
  classical
  let b := ⋃ x ∈ t, relativeIdealFiberSupport z d ((A).gluedBase d) ((A).universalFamily d) x
  have hb : b.Finite := finite_parameter_support z d ((A).gluedBase d)
    ((A).universalFamily d) t ht
  have hbW : b ⊆ W := by
    rintro y hy
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp hy
    exact (mem_universalAmbientSupport z d W x).mp (htW hx) hy
  let _ : Fact (LocallyFreeRankOne L) := ⟨hL.2.1⟩
  obtain ⟨U, hU, hbU, hUW⟩ := AmpleFiniteNeighborhood.of_ample L hL W hb.toFinset
    (fun x hx ↦ hbW (hb.mem_toFinset.mp hx))
  refine ⟨⟨U, hU⟩, hUW, ?_⟩
  rw [← universalAmbientSupport_affine]
  intro x hx
  apply (mem_universalAmbientSupport z d U x).mpr
  intro y hy
  exact hbU y (hb.mem_toFinset.mpr (Set.mem_iUnion₂.mpr ⟨x, hx, hy⟩))

include hL in
/-- Two common ambient charts have a single smaller ambient chart retaining all chosen points. -/
theorem exists_common_ambient_inter_refinement (U T : Z.affineOpens)
    (t : Set ((A).gluedHilbert d)) (ht : t.Finite)
    (hU : t ⊆ ((A).hilbertChart d U).opensRange)
    (hT : t ⊆ ((A).hilbertChart d T).opensRange) :
    ∃ B : Z.affineOpens, B.val ≤ U.val ⊓ T.val ∧
      t ⊆ ((A).hilbertChart d B).opensRange := by
  apply exists_common_ambient_refinement z d hL (U.val ⊓ T.val) t ht
  rw [universalAmbientSupport_inf, universalAmbientSupport_affine,
    universalAmbientSupport_affine]
  exact fun _ hx ↦ ⟨hU hx, hT hx⟩

end FLT.Mazur.HilbertChart

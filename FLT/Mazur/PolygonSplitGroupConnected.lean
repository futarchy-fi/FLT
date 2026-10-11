/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSplitGroup
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.AlgebraicGeometry.Properties

/-!
# The connected components of the actual split polygon group

Each full Laurent summand is open, closed and connected. Thus its image is
exactly the connected component of any of its points, including the identity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj
namespace FLT.Mazur.PolygonSplitGroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n]
local notation "T" => MultiplicativeGroupScheme.gm K

/-- A scheme coproduct summand is open and closed, with no equal-universe restriction. -/
theorem sigma_range_isClopen {I : Type*} [Small.{u} I] (X : I → Scheme.{u}) (i : I) :
    IsClopen (Set.range (Sigma.ι X i)) := by
  have hc : (Set.range (Sigma.ι X i))ᶜ =
      ⋃ j : {j : I // j ≠ i}, Set.range (Sigma.ι X j.val) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_range]
    constructor
    · intro hx
      obtain ⟨j, y, rfl⟩ := (sigmaOpenCover X).exists_eq x
      exact ⟨⟨j, fun h => hx (h ▸ ⟨y, rfl⟩)⟩, y, rfl⟩
    · rintro ⟨j, y, rfl⟩ ⟨z, hz⟩
      exact j.property (congrArg Sigma.fst ((sigmaι_eq_iff X i j.val z y).mp hz)).symm
  exact ⟨isOpen_compl_iff.mp (hc ▸ isOpen_iUnion (fun j =>
    (Sigma.ι X j.val).isOpenEmbedding.isOpen_range)),
    (Sigma.ι X i).isOpenEmbedding.isOpen_range⟩

/-- Each full multiplicative summand is open and closed in the actual split group. -/
theorem component_range_isClopen (i : ZMod n) :
    IsClopen (Set.range (component K n i).left) := by
  let c := sigmaComparison (Over.forget (Spec (.of K))) (fun _ : ZMod n => T)
  have h := ι_comp_sigmaComparison (Over.forget (Spec (.of K)))
    (fun _ : ZMod n => T) i
  change Sigma.ι (fun _ : ZMod n => (T).left) i ≫ c = (component K n i).left at h
  rw [← h]
  change IsClopen (Set.range (c ∘ Sigma.ι (fun _ : ZMod n => (T).left) i))
  rw [Set.range_comp]
  have hc := sigma_range_isClopen (fun _ : ZMod n => (T).left) i
  exact ⟨c.homeomorph.isClosedMap _ hc.1, c.homeomorph.isOpenMap _ hc.2⟩

omit [NeZero n] in
/-- Every full Laurent summand is connected over the field. -/
theorem component_range_isConnected (i : ZMod n) :
    _root_.IsConnected (Set.range (component K n i).left) := by
  let _ : ConnectedSpace (T).left :=
    inferInstanceAs (ConnectedSpace (Spec (.of (LaurentPolynomial K))))
  exact isConnected_range (component K n i).left.continuous

/-- A summand contains the entire connected component of each of its points. -/
theorem connectedComponent_component (i : ZMod n) (x : (T).left) :
    connectedComponent ((component K n i).left x) =
      Set.range (component K n i).left :=
  Set.Subset.antisymm ((component_range_isClopen K n i).connectedComponent_subset ⟨x, rfl⟩)
    ((component_range_isConnected K n i).subset_connectedComponent ⟨x, rfl⟩)

/-- The identity component is precisely the entire zeroth Laurent summand. -/
theorem connectedComponent_one (x : Spec (.of K)) :
    connectedComponent (η[model K n].left x) = Set.range (component K n 0).left := by
  change connectedComponent ((component K n 0).left (η[T].left x)) = _
  exact connectedComponent_component K n 0 _

/-- Every scheme realization retains the complete connected identity component. -/
theorem connectedComponent_iso_one {X : Scheme.{u}}
    (e : (model K n).left ≅ X) (x : Spec (.of K)) :
    connectedComponent (e.hom (η[model K n].left x)) =
      Set.range ((component K n 0).left ≫ e.hom) := by
  have hr : e.hom.homeomorph '' Set.range (component K n 0).left =
      Set.range ((component K n 0).left ≫ e.hom) := by
    rw [← Set.range_comp]
    rfl
  have hc : IsClopen (Set.range ((component K n 0).left ≫ e.hom)) := by
    rw [← hr]
    exact ⟨e.hom.homeomorph.isClosedMap _ (component_range_isClopen K n 0).1,
      e.hom.homeomorph.isOpenMap _ (component_range_isClopen K n 0).2⟩
  have hn : _root_.IsConnected (Set.range ((component K n 0).left ≫ e.hom)) := by
    rw [← hr]
    exact e.hom.homeomorph.isConnected_image.mpr (component_range_isConnected K n 0)
  have hx : e.hom (η[model K n].left x) ∈
      Set.range ((component K n 0).left ≫ e.hom) := ⟨η[T].left x, rfl⟩
  exact (hc.connectedComponent_subset hx).antisymm (hn.subset_connectedComponent hx)

end FLT.Mazur.PolygonSplitGroup

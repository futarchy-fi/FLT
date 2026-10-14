/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonActionSmooth
public import FLT.Mazur.PolygonSplitGroupConnected

/-!
# Connected components in the smooth locus of a specified pinching

The actual smooth-open inclusion sends each entire connected component to
its original punctured normalization component, including the identity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} [LocallyOfFinitePresentation C.hom]
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
local notation "e" => smoothIso K n hn p q h
local notation "T" => MultiplicativeGroupScheme.gm K

/-- Every point of a smooth Laurent summand has that entire summand as its component. -/
theorem smoothComponent_connectedComponent (i : ZMod n) (x : (T).left) :
    connectedComponent ((smoothComponent K n hn p q h i).left x) =
      Set.range (smoothComponent K n hn p q h i).left := by
  have he : (PolygonSplitGroup.component K n i ≫ (e).inv).left =
      (smoothComponent K n hn p q h i).left := by
    apply (cancel_mono C.hom.smoothLocus.ι).mp
    simpa only [PolygonSplitGroup.component, RingEquiv.apply_symm_apply] using
      (component_smoothIso_inv K n hn p q h ((ZMod.finEquiv n).symm i)).trans
        (smoothComponent_ι K n hn p q h i).symm
  have hc := PolygonSplitGroup.component_range_isClopen K n i
  have hn' := PolygonSplitGroup.component_range_isConnected K n i
  let E := ((Over.forget _).mapIso (e).symm).hom.homeomorph
  have hr : E '' Set.range (PolygonSplitGroup.component K n i).left =
      Set.range (smoothComponent K n hn p q h i).left := by
    rw [← Set.range_comp]
    exact congrArg (fun f : (T).left ⟶ C.hom.smoothLocus.toScheme => Set.range f) he
  have hc' : IsClopen (Set.range (smoothComponent K n hn p q h i).left) := by
    rw [← hr]
    exact ⟨E.isClosedMap _ hc.1, E.isOpenMap _ hc.2⟩
  have hn'' : _root_.IsConnected (Set.range (smoothComponent K n hn p q h i).left) := by
    rw [← hr]
    exact E.isConnected_image.mpr hn'
  exact (hc'.connectedComponent_subset ⟨x, rfl⟩).antisymm
    (hn''.subset_connectedComponent ⟨x, rfl⟩)

/-- The image of the full smooth component is the original punctured normalization image. -/
theorem smoothComponent_connectedComponent_image (i : ZMod n) (x : (T).left) :
    C.hom.smoothLocus.ι ''
        connectedComponent ((smoothComponent K n hn p q h i).left x) =
      Set.range (torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm i) ≫ p).left := by
  rw [smoothComponent_connectedComponent, ← Set.range_comp]
  exact congrArg (fun f : (T).left ⟶ C.left => Set.range f)
    (smoothComponent_ι K n hn p q h i)

/-- The split identity's connected component has exactly the zeroth punctured component image. -/
theorem smoothIdentity_connectedComponent_image (x : Spec (.of K)) :
    C.hom.smoothLocus.ι ''
        connectedComponent ((η[PolygonSplitGroup.model K n] ≫ (e).inv).left x) =
      Set.range (torusToComponent K ≫ componentι K n 0 ≫ p).left := by
  have he := PolygonSplitGroup.connectedComponent_iso_one K n
    ((Over.forget _).mapIso (e).symm) x
  change connectedComponent ((η[PolygonSplitGroup.model K n] ≫ (e).inv).left x) =
    Set.range (PolygonSplitGroup.component K n 0 ≫ (e).inv).left at he
  rw [he, ← Set.range_comp]
  have h0 : (ZMod.finEquiv n).symm 0 = 0 := by simp
  exact congrArg (fun f : (T).left ⟶ C.left => Set.range f) (by
    simpa only [PolygonActionSmooth.smoothMap, PolygonActionSmooth.smoothι,
      Over.comp_left, Over.homMk_left, h0, Category.assoc] using
      congrArg (fun f => f.left)
        (PolygonActionSmooth.component_smoothMap K n hn p q h 0))

end FLT.Mazur.PolygonPinching

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothOpenFieldCurveDimension
public import FLT.Mazur.SmoothNodalFamilyDimension
public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusBaseChange

/-!
# Relative dimension of the smooth open of a nodal family

The original connected geometric fibers have dimension one. Their smooth
opens need not be connected, but their dimension-one neighborhoods descend
to neighborhoods of every smooth point of the original affine-base family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.FCurve.CurveFiberHypotheses
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The entire smooth open of a nodal field fiber has relative dimension one. -/
theorem NodalFiberCore.smoothOpen_relativeDimension {K : Type} [Field K] {X : Scheme}
    {f : X ⟶ Spec (.of K)} (h : NodalFiberCore f) :
    let _ := h.finitePresentation
    SmoothOfRelativeDimension 1 (f.smoothLocus.ι ≫ f) := by
  let _ := h.finitePresentation
  let _ := h.connected
  let _ : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact f.smoothLocus.ι_preimage_self
  exact smooth_open_fieldCurve_relativeDimension f f.smoothLocus.ι
    h.pureDimension.topologicalKrullDim_eq_one

/-- Geometric nodal fibers give relative-curve neighborhoods of all original smooth points. -/
theorem NodalGeometricFibers.exists_dimensionOpen_spec
    {R : Type} [CommRing R] {X : Scheme} {f : X ⟶ Spec (.of R)}
    (h : NodalGeometricFibers f) [Flat f] [LocallyOfFinitePresentation f]
    (x : X) (hx : x ∈ f.smoothLocus) :
    ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension 1 (V.ι ≫ f) := by
  let K := AlgebraicClosure (X.residueField x)
  let p : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x
  let g := p ≫ f
  let a := (Spec.preimage g).hom
  let _ := a.toAlgebra
  have hg : Spec.map (CommRingCat.ofHom (algebraMap R K)) = g := Spec.map_preimage g
  let q := pullback.snd f g
  let i := pullback.fst f g
  let l : Spec (.of K) ⟶ Limits.pullback f g :=
    pullback.lift p (𝟙 _) (Category.id_comp _).symm
  have hi : i (l (IsLocalRing.closedPoint K)) = x := by
    change (l ≫ i) _ = x
    rw [pullback.lift_fst]
    exact X.fromSpecResidueField_apply x _
  let _ : SmoothOfRelativeDimension 1 ((i ⁻¹ᵁ f.smoothLocus).ι ≫ q) := by
    change SmoothOfRelativeDimension 1
      ((pullback.fst f g ⁻¹ᵁ f.smoothLocus).ι ≫ pullback.snd f g)
    rw [Scheme.Hom.preimage_smoothLocus_baseChange]
    exact (h.pullback g).smoothOpen_relativeDimension
  have hp : IsPullback i q f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [hg]
    exact .of_hasPullback f g
  obtain ⟨V, hV, hd⟩ := SmoothBaseChangeDimensionOpen.exists_open_at_smoothPoint
    f q i hp 1 (l (IsLocalRing.closedPoint K)) (by rw [hi]; exact hx)
  exact ⟨V, hi ▸ hV, hd⟩

/-- The whole smooth open over an affine base has relative dimension one across singular fibers. -/
theorem NodalGeometricFibers.smoothOpen_relativeDimension_spec
    {R : Type} [CommRing R] {X : Scheme} {f : X ⟶ Spec (.of R)}
    (h : NodalGeometricFibers f) [Flat f] [LocallyOfFinitePresentation f] :
    SmoothOfRelativeDimension 1 (f.smoothLocus.ι ≫ f) := by
  let U := f.smoothLocus
  have hd := fun x : U.toScheme ↦ h.exists_dimensionOpen_spec x.1 x.2
  choose V hx hV using hd
  have hc : (⨆ x, U.ι ⁻¹ᵁ V x) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun x ↦ U.ι ⁻¹ᵁ V x) hc
  intro x
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1) (hV x) _

end FLT.Mazur.FCurve.CurveFiberHypotheses

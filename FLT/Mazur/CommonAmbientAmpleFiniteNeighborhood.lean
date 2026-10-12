/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonAmbientSourceGrassmannianImmersion
public import FLT.Mazur.AmpleFiniteAffineNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Finite source neighborhoods from ampleness on the actual Grassmannian product

This bridge uses the established finite-set geometry of ample line bundles
on the actual target of the constructed immersion. The target line and its
ampleness are explicit inputs: their construction belongs to the geometric
lane. Closed pullback then gives one affine neighborhood of the entire
specified finite set, preserving its original common ambient support.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  (U : X.affineOpens)

/-- Target ampleness supplies a single actual affine neighborhood of a whole finite source set. -/
theorem exists_commonAmbient_affine_of_target_ample
    (M : (prod (commonAmbientGrassmannianTest f d U) V).left.Modules)
    (hM : AmpleLineBundle M) (t : Set (variableHilbertTest f d V).left)
    (ht : t.Finite) (hU : t ⊆ commonAmbientSourceOpen f d V U) :
    ∃ W : (variableHilbertTest f d V).left.Opens,
      IsAffineOpen W ∧ t ⊆ W ∧ W ≤ commonAmbientSourceOpen f d V U := by
  classical
  let F := (commonAmbientSourceGrassmannianMap f d V U).left
  let C := commonAmbientSourceGrassmannianClosedFactor f d V U
  let N := commonAmbientSourceGrassmannianNeighborhood f d V U
  let s : Set (commonAmbientSourceTest f d V U).left := {x | x.val ∈ t}
  have hs : s.Finite := ht.preimage Subtype.val_injective.injOn
  have hFs : (F '' s).Finite := hs.image F
  let _ : Fact (LocallyFreeRankOne M) := ⟨hM.2.1⟩
  obtain ⟨A, hA, hsA, hAN⟩ := AmpleFiniteNeighborhood.of_ample M hM N hFs.toFinset (by
    intro x hx
    obtain ⟨y, _, rfl⟩ := hFs.mem_toFinset.mp hx
    exact subset_coborder ⟨y, rfl⟩)
  have hNA : IsAffineOpen (N.ι ⁻¹ᵁ A) := hA.preimage_of_isOpenImmersion N.ι (by
    rwa [Scheme.Opens.opensRange_ι])
  let B := C ⁻¹ᵁ (N.ι ⁻¹ᵁ A)
  have hB : IsAffineOpen B := hNA.preimage C
  refine ⟨(commonAmbientSourceInclusion f d V U).left ''ᵁ B,
    hB.image_of_isOpenImmersion (commonAmbientSourceInclusion f d V U).left, ?_, ?_⟩
  · intro x hx
    let y : (commonAmbientSourceTest f d V U).left := ⟨x, hU hx⟩
    refine ⟨y, ?_, rfl⟩
    have hy : F y ∈ A := hsA (F y) (hFs.mem_toFinset.mpr ⟨y, hx, rfl⟩)
    change N.ι (C y) ∈ A
    rwa [← Scheme.Hom.comp_apply, commonAmbientSourceGrassmannianClosedFactor_ι]
  · rintro x ⟨y, _, rfl⟩
    exact y.property

end FLT.Mazur.HilbertChart

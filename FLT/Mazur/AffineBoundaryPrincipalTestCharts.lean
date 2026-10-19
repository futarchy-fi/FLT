/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryScalarNilpotence
public import FLT.Mazur.SchemeScalarAvoidanceCover
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Full affine charts where an original boundary test is invertible

Principal opens of the actual test coordinates give affine charts without
reducing the boundary product. Finite type of the original scalar map supplies
finite generators over the unchanged boundary scalars on each chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (t : B)

/-- The full principal open on which an original test coordinate is invertible. -/
def boundaryTestChart : (boundaryProduct s κ).Opens :=
  (boundaryProduct s κ).basicOpen (boundaryCoordinate s κ t)

instance boundaryTestChart_affine : IsAffine (boundaryTestChart s κ t).toScheme := by
  dsimp only [boundaryTestChart]
  infer_instance

/-- The original scalar map on the full principal test chart. -/
def boundaryTestChartScalar : T →+* Γ((boundaryTestChart s κ t).toScheme, ⊤) :=
  (boundaryTestChart s κ t).ι.appTop.hom.comp (boundaryScalarHom s κ)

/-- Recover the geometric projection from the unchanged scalar coordinate homomorphism. -/
theorem scalarMorphism_boundaryScalarHom :
    scalarMorphism (boundaryScalarHom s κ) = boundaryScalarProjection s κ := by
  rw [boundaryScalarHom, scalarMorphism_comp]
  change boundaryScalarProjection s κ ≫
    (Spec (.of T)).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (.of T)).inv = _
  rw [← Scheme.isoSpec_Spec_inv]
  change boundaryScalarProjection s κ ≫
    (Spec (.of T)).isoSpec.hom ≫ (Spec (.of T)).isoSpec.inv = _
  rw [Iso.hom_inv_id, Category.comp_id]

/-- The principal chart retains its actual projection to the original scalar spectrum. -/
theorem boundaryTestChartScalar_morphism :
    scalarMorphism (boundaryTestChartScalar s κ t) =
      (boundaryTestChart s κ t).ι ≫ boundaryScalarProjection s κ := by
  rw [boundaryTestChartScalar, scalarMorphism_comp, scalarMorphism_boundaryScalarHom]

/-- Membership in a full chart is nonvanishing of the original test at the original first prime. -/
theorem mem_boundaryTestChart (z : boundaryProduct s κ) :
    z ∈ boundaryTestChart s κ t ↔ t ∉ (boundaryProjection s κ z).asIdeal := by
  rw [boundaryTestChart, boundaryCoordinate_basicOpen]
  rfl

attribute [local irreducible] boundaryTestChart boundaryTestChartScalar

/-- Finite type survives the unchanged scalar base change and principal restriction. -/
theorem boundaryTestChartScalar_finiteType (hs : s.FiniteType) :
    (boundaryTestChartScalar s κ t).FiniteType := by
  let _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom s)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hs
  let _ : LocallyOfFiniteType (boundaryScalarProjection s κ) := by
    dsimp only [boundaryScalarProjection, boundaryProduct]
    exact MorphismProperty.pullback_snd (P := @LocallyOfFiniteType)
      (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom κ)) inferInstance
  let _ : LocallyOfFiniteType (scalarMorphism (boundaryTestChartScalar s κ t)) := by
    rw [boundaryTestChartScalar_morphism]
    infer_instance
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
    (φ := CommRingCat.ofHom (boundaryTestChartScalar s κ t))).mp
  have he : Spec.map (CommRingCat.ofHom (boundaryTestChartScalar s κ t)) =
      inv (boundaryTestChart s κ t).toScheme.toSpecΓ ≫
        scalarMorphism (boundaryTestChartScalar s κ t) := by
    rw [scalarMorphism, IsIso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-- A finite type ring map has a finite generating set including precisely its scalar image. -/
theorem finiteType_exists_scalar_generators {D E : Type} [CommRing D] [CommRing E]
    (σ : D →+* E) (hσ : σ.FiniteType) :
    ∃ a : Finset E, Subring.closure (Set.range σ ∪ (a : Set E)) = ⊤ := by
  let _ := σ.toAlgebra
  obtain ⟨a, ha⟩ := hσ.out
  refine ⟨a, ?_⟩
  change Subring.closure (Set.range (algebraMap D E) ∪ ↑a) = ⊤
  rw [← Algebra.adjoin_eq_ring_closure, ha]
  rfl

/-- Finite generators exist over the original scalar ring, without scalar Noetherianity. -/
theorem boundaryTestChart_exists_generators (hs : s.FiniteType) :
    ∃ a : Finset Γ((boundaryTestChart s κ t).toScheme, ⊤),
      Subring.closure (Set.range (boundaryTestChartScalar s κ t) ∪ (a : Set _)) = ⊤ :=
  finiteType_exists_scalar_generators _ (boundaryTestChartScalar_finiteType s κ t hs)

end FLT.Mazur.AffineScalarBoundaryNilpotence

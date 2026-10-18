/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverDenominators
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite original scalar generators on the constructed bad atlas

Local finite type over the integers forces finite type over any original
scalar ring. Thus the finite bad atlas has finite algebra generators even
without assuming that the ambient scheme is affine or the scalar ring is Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme.{0}} [NoetherianSpace X]
  (s : R →+* Γ(X, ⊤)) (O : X.Opens)
  (g : X ⟶ Spec (.of ℤ)) [LocallyOfFiniteType g]

include g in
/-- Every original bad-chart scalar map is finite type, derived from integer finite type. -/
theorem badChartScalar_finiteType (i : (badCover O).I₀) :
    (badChartScalar s O i).FiniteType := by
  let B := (badCover O).X i
  let t := badChartScalar s O i
  let z : Spec (.of R) ⟶ Spec (.of ℤ) := specZIsTerminal.from _
  have hg : LocallyOfFiniteType (badChartMap O i ≫ g) := by
    change LocallyOfFiniteType ((badCover O).f i ≫ badInclusion O ≫ g)
    infer_instance
  have he : scalarMorphism t ≫ z = badChartMap O i ≫ g := specZIsTerminal.hom_ext _ _
  have hcomp : LocallyOfFiniteType (scalarMorphism t ≫ z) := he ▸ hg
  let _ := locallyOfFiniteType_of_comp (scalarMorphism t) z
  have hspec : Spec.map (CommRingCat.ofHom t) =
      inv B.toSpecΓ ≫ scalarMorphism t := by
    rw [scalarMorphism, IsIso.inv_hom_id_assoc]
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
    (φ := CommRingCat.ofHom t)).mp
  rw [hspec]
  infer_instance

include g in
/-- A concrete finite set of generators exists over the unchanged original scalar map. -/
theorem exists_badChart_finite_generators (i : (badCover O).I₀) :
    ∃ b : Finset Γ((badCover O).X i, ⊤),
      Subring.closure (Set.range (badChartScalar s O i) ∪ (b : Set _)) = ⊤ := by
  let _ := (badChartScalar s O i).toAlgebra
  have h := badChartScalar_finiteType s O g i
  obtain ⟨b, hb⟩ := h.out
  refine ⟨b, ?_⟩
  change Subring.closure (Set.range (algebraMap R Γ((badCover O).X i, ⊤)) ∪ ↑b) = ⊤
  rw [← Algebra.adjoin_eq_ring_closure, hb]
  rfl

/-- Choose the proven finite generators once, before choosing any original prime. -/
def badChartGenerators (i : (badCover O).I₀) : Finset Γ((badCover O).X i, ⊤) :=
  (exists_badChart_finite_generators s O g i).choose

/-- The chosen generators span over precisely the original scalar map. -/
theorem badChartGenerators_generate (i : (badCover O).I₀) :
    Subring.closure (Set.range (badChartScalar s O i) ∪
      (badChartGenerators s O g i : Set _)) = ⊤ :=
  (exists_badChart_finite_generators s O g i).choose_spec

end FLT.Mazur.SchemeBadAffineCover

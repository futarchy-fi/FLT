/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperIntegralConstantSections
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Separation.Connected

/-!
# Constant functions on connected reduced proper schemes

The global section ring is finite over the base field. Its spectrum is discrete
and is a continuous image of the connected proper scheme, hence is a point.
Reducedness then makes it a field. Evaluation at a rational section identifies
this field with the base field; no irreducibility assumption is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
variable {K : Type} [Field K] {X : Scheme} (f : X ⟶ Spec (.of K))
  [IsProper f] [IsReduced X] [ConnectedSpace X]

include f in
/-- The global section ring of a connected reduced proper scheme is a field. -/
theorem globalSections_isField_of_proper_connected_reduced : IsField Γ(X, ⊤) := by
  let _ := (structureScalarMap f).toAlgebra
  let _ : Module.Finite K Γ(X, ⊤) :=
    finiteDimensional_globalSections_of_proper f
  let _ : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K _
  let _ : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  have : UniversallyClosed X.toSpecΓ :=
    .of_comp_of_isSeparated _ (Spec.map f.appTop)
  have : Nontrivial Γ(X, ⊤) := (X.Γevaluation (Classical.arbitrary X)).hom.domain_nontrivial
  let _ : ConnectedSpace (Spec Γ(X, ⊤)) :=
    (Surjective.surj (f := X.toSpecΓ)).connectedSpace X.toSpecΓ.continuous
  let _ : ConnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    inferInstanceAs (ConnectedSpace (Spec Γ(X, ⊤)))
  let _ : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := PreconnectedSpace.trivial_of_discrete
  exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp inferInstance

/-- A global function is determined by its value at the specified rational point. -/
theorem scalar_sectionEvaluation_of_connected_reduced
    (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) (a : Γ(X, ⊤)) :
    structureScalarMap f (sectionEvaluation s a) = a := by
  let _ := (globalSections_isField_of_proper_connected_reduced f).toField
  apply (sectionEvaluation s).injective
  exact DFunLike.congr_fun (sectionEvaluation_scalar f s hs) (sectionEvaluation s a)

/-- Connectedness and reducedness suffice for the actual pointed H0 comparison. -/
theorem constantGlobalSections_of_proper_connected_reduced_section
    (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) : HasConstantGlobalSections f := by
  have : Nontrivial Γ(X, ⊤) := (sectionEvaluation s).domain_nontrivial
  refine ⟨(structureScalarMap f).injective, fun a ↦ ?_⟩
  exact ⟨sectionEvaluation s a, scalar_sectionEvaluation_of_connected_reduced f s hs a⟩

end FLT.Mazur.FCurve

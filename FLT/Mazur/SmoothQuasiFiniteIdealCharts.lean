/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySmoothQuasiFiniteCartier
public import FLT.Mazur.CartierIdealStalkNeighborhood

/-!
# Scheme Cartier charts for quasi-finite flat quotient ideals

Smooth curve coordinates and a finite presentation of the full ideal
construct Cartier neighborhoods without assuming an affine ambient morphism
or a finite quotient on the chosen affine open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f]

/-- A presented ideal with quasi-finite flat quotient supplies Cartier neighborhoods. -/
theorem cartierChart_neighborhood_of_smooth_quasiFinite_flat (I : X.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    [Module.FinitePresentation Γ(X, V) (I.ideal V)]
    (hqf : let _ := (f.appLE U V e).hom.toAlgebra
      Algebra.QuasiFinite Γ(Y, U) (Γ(X, V) ⧸ I.ideal V))
    (hflat : let _ := (f.appLE U V e).hom.toAlgebra
      Module.Flat Γ(Y, U) (Γ(X, V) ⧸ I.ideal V))
    (x : X) (hx : x ∈ V.1) :
    ∃ r : Γ(X, V), x ∈ X.basicOpen r ∧ CartierChart I (X.affineBasicOpen r) := by
  let _ : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let _ := (f.appLE U V e).hom.toAlgebra
  let _ := hqf
  let _ := hflat
  have hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap Γ(Y, U) Γ(X, V)) :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) f inferInstance U V e
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  let _ := V.2.isLocalization_stalk ⟨x, hx⟩
  let q := (V.2.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨a, ha, hIa⟩ := regular_generator_locallySmooth_quasiFinite_flat_atPrime hsm (I.ideal V) q
  obtain ⟨b, hb, hIb⟩ := regular_generator_localization_transport
    (B := X.presheaf.stalk x) q.primeCompl (I.ideal V) a ha hIa
  apply cartierChart_neighborhood_of_stalk I V x hx
  refine ⟨b, hb, ?_⟩
  rw [stalkIdeal_eq_map I x V hx]
  exact hIb

end FLT.Mazur.FCurve

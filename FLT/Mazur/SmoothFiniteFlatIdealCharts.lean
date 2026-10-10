/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePresentedFlatQuotientIdeal
public import FLT.Mazur.LocallySmoothFiniteFlatCartier
public import FLT.Mazur.CartierIdealStalkNeighborhood

/-!
# Scheme Cartier charts from actual finite flat affine quotients

Smoothness of the scheme morphism constructs the local standard-smooth
coordinates. Finite presentation and flatness of the actual affine quotient
construct the ideal presentation and a Cartier neighborhood in the scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f]

/-- The actual quotient on a smooth affine chart supplies scheme Cartier neighborhoods. -/
theorem cartierChart_neighborhood_of_smooth_finite_flat (I : X.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (hfp : let _ := (f.appLE U V e).hom.toAlgebra
      Module.FinitePresentation Γ(Y, U) (Γ(X, V) ⧸ I.ideal V))
    (hflat : let _ := (f.appLE U V e).hom.toAlgebra
      Module.Flat Γ(Y, U) (Γ(X, V) ⧸ I.ideal V))
    (x : X) (hx : x ∈ V.1) :
    ∃ r : Γ(X, V), x ∈ X.basicOpen r ∧ CartierChart I (X.affineBasicOpen r) := by
  let _ : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let _ := (f.appLE U V e).hom.toAlgebra
  let _ := hfp
  let _ := hflat
  let _ : Algebra.FinitePresentation Γ(Y, U) Γ(X, V) :=
    f.finitePresentation_appLE U.2 V.2 e
  have hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap Γ(Y, U) Γ(X, V)) :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) f inferInstance U V e
  let _ := ideal_finitePresentation_of_finitePresentation_flat_quotient
    (R := Γ(Y, U)) (I.ideal V)
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  let _ := V.2.isLocalization_stalk ⟨x, hx⟩
  let q := (V.2.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨a, ha, hIa⟩ := regular_generator_locallySmooth_finite_flat_atPrime hsm (I.ideal V) q
  obtain ⟨b, hb, hIb⟩ := regular_generator_localization_transport
    (B := X.presheaf.stalk x) q.primeCompl (I.ideal V) a ha hIa
  apply cartierChart_neighborhood_of_stalk I V x hx
  refine ⟨b, hb, ?_⟩
  rw [stalkIdeal_eq_map I x V hx]
  exact hIb

end FLT.Mazur.FCurve

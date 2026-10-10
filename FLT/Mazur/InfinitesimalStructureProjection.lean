/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StructureIdealPowerQuotient
public import FLT.Mazur.BaseAdicCohomologyFiltration
public import FLT.Mazur.BaseAdicQuotientSpectrum
public import FLT.Mazur.NoetherianInfinitesimalFiberFunctions

/-!
# Infinitesimal fiber vanishing in the original adic quotient

For a pointed proper flat family over a Noetherian ring with geometrically
connected reduced fibers, an evaluation-zero function maps to zero under the
actual structure-module projection for every maximal-ideal power.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.BaseAdicThickening
namespace FLT.Mazur.InfinitesimalStructureProjection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : CommRingCat.{0}} [IsNoetherianRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec R) [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)
  (J : Ideal R) [J.IsMaximal] (n : ℕ)

include hs

/-- Evaluation-zero functions vanish on the actual extended-ideal thickening. -/
theorem immersion_eq_zero (x : Γ(X, ⊤)) (hx : s.appTop x = 0) :
    ((baseIdeal R J).comap f ^ n).subschemeι.appTop x = 0 := by
  let a := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n)))
  let _ := NoetherianInfinitesimalFiberFunctions.quotient_pow_artinian J n
  let _ : IsArtinianRing Γ(Spec (.of (R ⧸ J ^ n)), ⊤) :=
    (Scheme.ΓSpecIso (.of (R ⧸ J ^ n))).symm.commRingCatIsoToRingEquiv.isArtinianRing
  have hb : Function.Bijective (pullback.snd f a).appTop :=
    ArtinianProperRelativeFunctions.appTop_bijective _
      (SchemeProperGeometricFiberSections.baseChangedSection f s hs a)
      (SchemeProperGeometricFiberSections.baseChangedSection_projection f s hs a)
  have hz := NoetherianInfinitesimalFiberFunctions.pullback_eq_zero_of_bijective
    f s hs a hb x hx
  rw [← quotientPullbackIso_hom_fst R J f n, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, hz, map_zero]

/-- Actual geometric vanishing kills the original structure-module quotient projection. -/
theorem projection_eq_zero (x : Γ(X, ⊤)) (hx : s.appTop x = 0) :
    let _ := Chow.source_isNoetherian f
    (IdealAdicQuotient.projection ((baseIdeal R J).comap f)
      (structureModule X) n).app ⊤ x = 0 := by
  let _ := Chow.source_isNoetherian f
  exact (StructureIdealPowerQuotient.projection_eq_zero_iff _ n x).mpr
    (immersion_eq_zero f s hs J n x hx)

/-- The corresponding original H0 class lies in every geometric image-filtration term. -/
theorem mem_cohomologyImage (x : Γ(X, ⊤)) (hx : s.appTop x = 0) :
    let _ := Chow.source_isNoetherian f
    let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
    (moduleH0Equiv (structureModule X)).symm x ∈
      IdealAdicQuotient.cohomologyImage (Chow.AffineBase.baseCohomologyScalars f)
        ((baseIdeal R J).comap f) (structureModule X) 0 n := by
  let _ := Chow.source_isNoetherian f
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  apply (IdealAdicQuotient.mem_cohomologyImage_iff _ _ _ 0 n _).mpr
  apply (moduleH0Equiv _).injective
  rw [moduleH0Equiv_naturality, LinearEquiv.apply_symm_apply, map_zero]
  exact projection_eq_zero f s hs J n x hx

end FLT.Mazur.InfinitesimalStructureProjection

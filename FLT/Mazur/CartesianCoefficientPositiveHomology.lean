/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechModuleHomology
public import FLT.Mazur.IncreasingCechCoefficientKernel

/-!
# Positive coefficient cohomology on actual cartesian charts

The existing cartesian term maps form an isomorphism of the actual adjacent
module complexes. For flat affine base change this identifies tensorized
bounded coefficient cohomology with bounded cohomology on the inverse-image cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open IncreasingCechScalars FCurve
open Scheme.Modules hiding map_smul
variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S] [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

/-- Actual cartesian term maps give an isomorphism of adjacent module complexes. -/
def geometricPositiveComplexIso (n : ℕ) :
    (positiveModuleComplex M U f.appTop.hom n).map
      (ModuleCat.extendScalars g.appTop.hom) ≅
        positiveModuleComplex ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n :=
  ShortComplex.isoMk (geometricTermEquiv h M U hU n).toModuleIso
    (geometricTermEquiv h M U hU (n + 1)).toModuleIso
    (geometricTermEquiv h M U hU (n + 1 + 1)).toModuleIso
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (geometricTermEquiv_d h M U hU n x).symm)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (geometricTermEquiv_d h M U hU (n + 1) x).symm)

/-- Flat affine base change commutes with actual positive bounded coefficient cohomology. -/
def flatGeometricPositiveHomologyIso (hg : g.appTop.hom.Flat) (n : ℕ) :
    (ModuleCat.extendScalars g.appTop.hom).obj
      (ModuleCat.of Γ(S, ⊤) (BaseHomology M U f.appTop.hom (n + 1))) ≅
        ModuleCat.of Γ(T, ⊤) (BaseHomology ((pullback p).obj M)
          (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom (n + 1)) :=
  flatPositiveHomologyIso M U f.appTop.hom g.appTop.hom hg n ≪≫
    (ShortComplex.homologyFunctor _).mapIso (geometricPositiveComplexIso h M U hU n) ≪≫
      (positiveModuleHomologyEquiv ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i)
        q.appTop.hom n).toModuleIso

end FLT.Mazur.IncreasingCechCoefficients

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechModuleHomology
public import FLT.Mazur.IncreasingCechCartesianKernel

/-!
# Positive structure cohomology on actual cartesian charts

The existing cartesian term maps form an isomorphism of the actual adjacent
module complexes. For flat affine base change this identifies tensorized
bounded structure cohomology with bounded cohomology on the inverse-image cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCartesian
open IncreasingCechScalars FCurve
variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S] [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g)
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

/-- Actual cartesian term maps give an isomorphism of adjacent module complexes. -/
def geometricPositiveComplexIso (n : ℕ) :
    (positiveModuleComplex (structureModule X) U f.appTop.hom n).map
      (ModuleCat.extendScalars g.appTop.hom) ≅
        positiveModuleComplex (structureModule P) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n :=
  ShortComplex.isoMk (geometricTermEquiv h U hU n).toModuleIso
    (geometricTermEquiv h U hU (n + 1)).toModuleIso
    (geometricTermEquiv h U hU (n + 1 + 1)).toModuleIso
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (geometricTermEquiv_d h U hU n x).symm)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (geometricTermEquiv_d h U hU (n + 1) x).symm)

/-- Flat affine base change commutes with actual positive bounded structure cohomology. -/
def flatGeometricPositiveHomologyIso (hg : g.appTop.hom.Flat) (n : ℕ) :
    (ModuleCat.extendScalars g.appTop.hom).obj
      (ModuleCat.of Γ(S, ⊤) (BaseHomology (structureModule X) U f.appTop.hom (n + 1))) ≅
        ModuleCat.of Γ(T, ⊤) (BaseHomology (structureModule P)
          (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom (n + 1)) :=
  flatPositiveHomologyIso (structureModule X) U f.appTop.hom g.appTop.hom hg n ≪≫
    (ShortComplex.homologyFunctor _).mapIso (geometricPositiveComplexIso h U hU n) ≪≫
      (positiveModuleHomologyEquiv (structureModule P) (fun i ↦ p ⁻¹ᵁ U i)
        q.appTop.hom n).toModuleIso

end FLT.Mazur.IncreasingCechCartesian

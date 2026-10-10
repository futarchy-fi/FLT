/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechTensorCoordinates
public import FLT.Mazur.CartesianSectionRestriction
public import FLT.Mazur.AffineCoverIntersections

/-!
# Actual cartesian sections of increasing charts

Every tensor term maps to sections on the inverse images of the original
increasing chart intersections. Affineness makes this map bijective for any
change of base, including nonflat ones.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.IncreasingCechCoefficients
open IncreasingCechComplex IncreasingCechScalars FCurve Chow CechSheafHZero
open CartesianOpenSectionMap
open Scheme.Modules hiding map_smul

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules)
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)

/-- Tensor coordinates retain the coefficient-ring action. -/
def scalarTensorCoordinates (n : ℕ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] BaseTerm M U f.appTop.hom n ≃ₗ[Γ(T, ⊤)]
      (∀ a : Tuple (ι := ι) n,
        Γ(T, ⊤) ⊗[Γ(S, ⊤)] baseSections M f.appTop.hom (V U n a.val)) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let _ := Fintype.ofFinite (Tuple (ι := ι) n)
  exact (AlgebraTensorModule.congr (LinearEquiv.refl Γ(T, ⊤) Γ(T, ⊤))
    (baseTermCoordinates M U f.appTop.hom n)).trans
      (piRight Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤) _)

/-- The actual inverse-image chart section product. -/
abbrev ChartTerm (n : ℕ) :=
  ∀ a : Tuple (ι := ι) n, baseSections ((pullback p).obj M) q.appTop.hom (p ⁻¹ᵁ V U n a.val)

/-- Compare a tensor term to actual sections on each cartesian chart. -/
def termComparison (n : ℕ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] BaseTerm M U f.appTop.hom n →ₗ[Γ(T, ⊤)]
      ChartTerm (p := p) (q := q) M U n := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact
    { toFun := fun x a ↦ comparison h M (V U n a.val)
        (scalarTensorCoordinates (g := g) M U n x a)
      map_add' := fun x y ↦ by
        funext a
        simp only [map_add, Pi.add_apply]
      map_smul' := fun b x ↦ by
        funext a
        rw [map_smul, Pi.smul_apply]
        exact (comparison h M (V U n a.val)).hom.map_smul b _ }

/-- On pure tensors the chart map is scalar multiplication of actual pulled-back sections. -/
lemma termComparison_tmul (n : ℕ) (b : Γ(T, ⊤))
    (x : BaseTerm M U f.appTop.hom n) (a : Tuple (ι := ι) n) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    termComparison h M U n (b ⊗ₜ[Γ(S, ⊤)] x) a =
      b • (show OpenModuleSectionScalars.openSections q ((pullback p).obj M)
        (p ⁻¹ᵁ V U n a.val) from
          ((pullbackPushforwardAdjunction p).unit.app M).app (V U n a.val) (x a)) :=
  comparison_tmul h M _ b (x a)

include h in
/-- Actual finite affine charts identify every tensor term, without flat base change. -/
lemma termComparison_bijective [IsAffine T] [IsAffine S] [X.IsSeparated]
    [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    Function.Bijective (termComparison h M U n) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  have hc := fun a : Tuple (ι := ι) n ↦ by
    let _ := comparison_isIso h M (V U n a.val)
      (affineCover_intersection_isAffineOpen U hU n a.val)
    exact ConcreteCategory.bijective_of_isIso (comparison h M (V U n a.val))
  constructor
  · intro x y hxy
    apply (scalarTensorCoordinates (g := g) M U n).injective
    funext a
    exact (hc a).injective (congrFun hxy a)
  · intro y
    choose x hx using fun a ↦ (hc a).surjective (y a)
    refine ⟨(scalarTensorCoordinates (g := g) M U n).symm x, ?_⟩
    funext a
    have he := congrFun ((scalarTensorCoordinates (g := g) M U n).apply_symm_apply x) a
    exact (congrArg (comparison h M (V U n a.val)) he).trans (hx a)

end FLT.Mazur.IncreasingCechCoefficients

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCartesianTerms

/-!
# Cartesian chart differential compatibility

The term comparison carries the tensorized bounded differential to the signed
sum of actual restrictions on the inverse-image chart intersections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.IncreasingCechCartesian
open IncreasingCechComplex IncreasingCechScalars FCurve Chow CechSheafHZero
open CartesianStructureSections

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g)
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)

/-- Restrict from a deleted chart to the full inverse-image intersection. -/
def chartCoface (n : ℕ) (k : Fin (n + 2)) :
    ChartTerm (p := p) (q := q) U n →ₗ[Γ(T, ⊤)] ChartTerm (p := p) (q := q) U (n + 1) :=
  LinearMap.pi (fun a ↦
    (baseRestriction (structureModule P) q.appTop.hom
      (p.preimage_mono (face_le U n a.val k))).comp (LinearMap.proj (face a k)))

/-- The differential uses the original signs and actual cartesian restrictions. -/
def chartD (n : ℕ) :
    ChartTerm (p := p) (q := q) U n →ₗ[Γ(T, ⊤)] ChartTerm (p := p) (q := q) U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • chartCoface U n k

omit [Finite ι] in
/-- Coordinates of the actual cartesian chart differential. -/
lemma chartD_apply (n : ℕ) (x : ChartTerm (p := p) (q := q) U n)
    (a : Tuple (ι := ι) (n + 1)) :
    chartD U n x a = ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      baseRestriction (structureModule P) q.appTop.hom
        (p.preimage_mono (face_le U n a.val k)) (x (face a k)) := by
  simp only [chartD, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, chartCoface, LinearMap.pi_apply, LinearMap.comp_apply]
  rfl

/-- The term comparison intertwines tensor differentials and actual chart restrictions. -/
lemma termComparison_d (n : ℕ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ x : Γ(T, ⊤) ⊗[Γ(S, ⊤)] BaseTerm (structureModule X) U f.appTop.hom n,
      termComparison h U (n + 1) ((baseD (structureModule X) U f.appTop.hom n).lTensor
        Γ(T, ⊤) x) = chartD U n (termComparison h U n x) := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro x
  funext a
  change comparison h (V U (n + 1) a.val)
    (tensorCoordinates (structureModule X) U f.appTop.hom Γ(T, ⊤) (n + 1)
      ((baseD (structureModule X) U f.appTop.hom n).lTensor Γ(T, ⊤) x) a) = _
  rw [tensorD_coordinates, map_sum, chartD_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul]
  congr 1
  exact comparison_lTensor h (face_le U n a.val k) _

end FLT.Mazur.IncreasingCechCartesian

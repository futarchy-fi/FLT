/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianLocallyFramedQuotient
public import FLT.Mazur.GrassmannianQuotientRecoveryStatement

/-!
# Global scheme classification and recovery of locally free quotients

A quotient given only as a global ambient epimorphism and pointwise fixed-rank
frames constructs a scheme morphism whose actual descended quotient is the
original sheaf. The isomorphism retains the entire global ambient projection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOpenChartDescent
open GrassmannianChart
universe u
variable {R M ι κ τ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] [Fintype τ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P) [Epi p]
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf
  ambientClassifyingMap ambientMorphismPoint

/-- Every pointwise fixed-rank locally free ambient quotient is an actual quotient image. -/
theorem exists_locallyFreeQuotientRecovery
    (hP : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (P.restrict U.ι ≅ SheafOfModules.free τ)) (hd : Fintype.card τ = d) :
    ∃ (f : X ⟶ ambientGrassmannianScheme R M κ d)
      (hf : f ≫ ambientGrassmannianStructure R M κ d = β)
      (C : X.AffineOpenCover.{u}) (a : ∀ j, Algebra R (C.X j)),
      let _ := a
      ∃ (N : ∀ j, Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d)
        (h : ∀ j, C.f j ≫ f = ambientClassifyingMap b (N j) hκ),
        PresentedQuotientRecovers b hκ β p C N f hf h := by
  obtain ⟨f, hf, C, a, hC, N, h, he⟩ :=
    exists_locallyFramedQuotientClassifying β p hP hd b hκ
  let _ := a
  let e := fun j ↦ (he j).choose
  have he' := fun j ↦ (he j).choose_spec
  exact ⟨f, hf, C, a, N, h,
    presentedQuotientRecovers_of_charts b hκ β p C hC N f hf h e he'⟩

end FLT.Mazur.GrassmannianOpenChartDescent

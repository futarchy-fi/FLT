/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTensorCoalgebraComparison
public import FLT.Mazur.AffineLineCoalgebraDescent

/-!
# Compatible morphisms of affine tensor descent data

Compatibility on the double overlap is equivalent to compatibility with the
coaction. Such maps therefore descend uniquely through faithfully flat module
descent. The geometric pullback comparison remains a separate obligation.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u

namespace FLT.Mazur.AffineTensorCocycle

variable {R S M N : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- A map commutes with the coactions exactly when it commutes with the full overlaps. -/
theorem coaction_comm_iff (D : Datum R S M) (E : Datum R S N) (f : M →ₗ[S] N) :
    (∀ m, (f.restrictScalars R).lTensor S (D.coaction m) = E.coaction (f m)) ↔
      (∀ m s, (f.restrictScalars R).lTensor S (D.overlap (m ⊗ₜ[R] s)) =
        E.overlap (f m ⊗ₜ[R] s)) := by
  constructor
  · intro h m s
    rw [D.overlap_tmul, E.overlap_tmul, ← h]
    generalize D.coaction m = x
    induction x using TensorProduct.inductionOn with
    | tmul a n => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro h m
    exact h m 1

section Coalgebra

variable {A B : CommRingCat.{u}} (φ : A ⟶ B) (M N : ModuleCat.{u} B)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- An overlap-compatible coefficient map defines a morphism of the associated coalgebras. -/
def toCoalgebraHom :
    letI := φ.hom.toAlgebra
    letI := Module.compHom M φ.hom
    letI := Module.compHom N φ.hom
    letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    ∀ (D : Datum A B M) (E : Datum A B N) (f : M ⟶ N),
      (∀ m s, (f.hom.restrictScalars A).lTensor B (D.overlap (m ⊗ₜ[A] s)) =
        E.overlap (f m ⊗ₜ[A] s)) → (toCoalgebra φ M D ⟶ toCoalgebra φ N E) := by
  letI := φ.hom.toAlgebra
  letI := Module.compHom M φ.hom
  letI := Module.compHom N φ.hom
  letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  intro D E f hf
  refine { f := f, h := ?_ }
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact (coaction_comm_iff D E f.hom).mpr hf m

end Coalgebra

end FLT.Mazur.AffineTensorCocycle

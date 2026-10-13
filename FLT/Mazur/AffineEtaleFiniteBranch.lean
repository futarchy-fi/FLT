/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchEmbedding

/-!
# Finite etale branches through points of affine etale morphisms

Every point of an actual affine etale morphism has an etale neighborhood
which is finite etale over an etale change of the original target. The
commuting square retains the original morphism, not just its point map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
universe u
namespace FLT.Mazur.AffineEtaleFiniteBranch
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [Etale f]

/-- Construct a finite etale branch of the original affine map through any chosen point. -/
theorem exists_branch (x : X) :
    ∃ (Z W : Scheme.{u}) (b : W ⟶ Y) (t : Z ⟶ W) (a : Z ⟶ X) (z : Z),
      IsAffine Z ∧ IsAffine W ∧ Etale b ∧ Etale t ∧ IsFinite t ∧ Etale a ∧
        a ≫ f = t ≫ b ∧ a z = x ∧
        ∃ j : Z ⟶ pullback b f, IsOpenImmersion j ∧ IsClosedImmersion j ∧
          j ≫ pullback.fst b f = t ∧ j ≫ pullback.snd b f = a := by
  let A := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  let _ : Algebra A B := f.appTop.hom.toAlgebra
  have hf : f.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  let _ : Algebra.Etale A B := hf
  let q := (X.isoSpec.hom x).asIdeal
  let _ : q.IsPrime := (X.isoSpec.hom x).isPrime
  obtain ⟨C, hC, hAC, hEt, P, hP, hPq, e, he, Q, hQ,
      hQq, hQP, hres, hfin, het, huniq⟩ := EtaleAlgebraFiniteBranch.exists_branch (A := A) q
  let Z := EtaleFiniteBranchScheme.branch e
  let W := Spec (.of C)
  let b : W ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ Y.isoSpec.inv
  let a : Z ⟶ X := EtaleFiniteBranchScheme.original e ≫ X.isoSpec.inv
  let t : Z ⟶ W := EtaleFiniteBranchScheme.coefficient e
  let z : Z := ⟨Q, hQ⟩
  let _ : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr hEt)
  refine ⟨Z, W, b, t, a, z, inferInstanceAs (IsAffine (Spec _)), inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · dsimp only [a, b, t]
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc]
    exact congrArg (· ≫ Y.isoSpec.inv) (EtaleFiniteBranchScheme.condition e)
  · have hz : EtaleFiniteBranchScheme.original e z = X.isoSpec.hom x :=
      PrimeSpectrum.ext hQq
    change X.isoSpec.inv (EtaleFiniteBranchScheme.original e z) = x
    rw [hz, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  · let v := Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B)))
    let w := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom)
    have H : IsPullback v (w ≫ X.isoSpec.inv) b f := by
      apply EtaleFiniteBranchScheme.tensor_isPullback.of_iso
        (Iso.refl _) (Iso.refl _) X.isoSpec.symm Y.isoSpec.symm
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl
      · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
        rfl
      · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
        rfl
      · exact Scheme.isoSpec_inv_naturality f
    let j : Z ⟶ pullback b f := EtaleFiniteBranchScheme.inclusion e ≫ H.isoPullback.hom
    let _ := EtaleFiniteBranchScheme.inclusion_isClosedImmersion e he
    refine ⟨j, inferInstance, inferInstance, ?_, ?_⟩
    · dsimp only [j]
      rw [Category.assoc, IsPullback.isoPullback_hom_fst]
      exact EtaleFiniteBranchScheme.inclusion_coefficient e
    · dsimp only [j]
      rw [Category.assoc, IsPullback.isoPullback_hom_snd]
      exact (Category.assoc _ _ _).symm

end FLT.Mazur.AffineEtaleFiniteBranch

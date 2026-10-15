/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothFiberEtaleOpenPoint

/-!
# Original étale lifts meeting an arbitrary geometric smooth open

The geometric base map need not be supplied as a residue-field factorization.
Its kernel constructs that factorization, while the lift retains the original
open and the entire geometric base map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothGeometricOpenEtaleLift
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [IsSepClosed K]
  {V Y U : Scheme}

/-- A nonempty geometric smooth open is met by an affine étale original test. -/
theorem exists_lift (f : V ⟶ Spec (.of R)) [Smooth f]
    (t : Spec (.of K) ⟶ Spec (.of R)) (a : Y ⟶ V) (b : Y ⟶ Spec (.of K))
    (H : IsPullback a b f t) (j : U ⟶ Y) [IsOpenImmersion j] (hne : Nonempty U) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ V)
      (z : Spec (.of K) ⟶ E) (u : Spec (.of K) ⟶ U),
      IsAffine E ∧ Etale e ∧ v ≫ f = e ∧ z ≫ e = t ∧
      u ≫ j ≫ b = 𝟙 _ ∧ z ≫ v = u ≫ j ≫ a := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
  let p := RingHom.ker ψ.hom
  let _ : p.IsPrime := RingHom.ker_isPrime ψ.hom
  have hu : p.primeCompl ≤ (IsUnit.submonoid K).comap ψ.hom := by
    intro r hr
    change IsUnit (ψ.hom r)
    exact isUnit_iff_ne_zero.mpr hr
  let θ := Ideal.ResidueField.lift p ψ.hom le_rfl hu
  let _ := θ.toAlgebra
  have he : (algebraMap p.ResidueField K).comp (algebraMap R p.ResidueField) = ψ.hom := by
    ext r
    exact Ideal.ResidueField.lift_algebraMap p ψ.hom le_rfl hu r
  have H' : IsPullback a b f
      (Spec.map (CommRingCat.ofHom
        ((algebraMap p.ResidueField K).comp (algebraMap R p.ResidueField)))) := by
    rw [he]
    exact H
  have h := SmoothFiberEtaleOpenPoint.exists_point f (algebraMap R p.ResidueField)
    p.surjectiveOnStalks_residueField a b H' j hne
  rw [he] at h
  exact h

end FLT.Mazur.SmoothGeometricOpenEtaleLift

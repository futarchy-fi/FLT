/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtalePolynomialPointLift
public import FLT.Mazur.EtaleSeparableResidueCoordinates

/-!
# Étale polynomial slices through separable residue extensions

The coefficient extension is constructed by lifting minimal polynomials and
adjoining simple roots. Slicing the original étale coordinates over it retains
the entire field-valued point, beyond the residue-rational case.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtalePolynomialSeparableLift
set_option backward.isDefEq.respectTransparency false
variable {R B k K : Type} [CommRing R] [CommRing B] [Field k] [Field K] [Algebra k K]

/-- Separable residue coordinates extend to constructed étale neighborhoods of the original base. -/
theorem exists_lift {n : ℕ} (g : MvPolynomial (Fin n) R →+* B) (hg : g.Etale)
    (q : B →+* K) (φ : R →+* k) (hφ : φ.SurjectiveOnStalks)
    (hq : q.comp (g.comp MvPolynomial.C) = (algebraMap k K).comp φ)
    (hs : ∀ i, IsSeparable k (q (g (MvPolynomial.X i)))) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ Spec (.of B))
      (z : Spec (.of K) ⟶ E),
      Etale e ∧ v ≫ Spec.map (CommRingCat.ofHom (g.comp MvPolynomial.C)) = e ∧
        z ≫ e = Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)) ∧
        z ≫ v = Spec.map (CommRingCat.ofHom q) := by
  obtain ⟨A, α, ψ, a, hα, hψ, ha⟩ :=
    EtaleSeparableResidueCoordinates.exists_coordinates φ hφ
      (fun i : Fin n ↦ q (g (MvPolynomial.X i))) hs
  let G := Spec.map (CommRingCat.ofHom g)
  let P := Spec.map
    (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
  let u := Spec.map (CommRingCat.ofHom α)
  let t := Spec.map
    (CommRingCat.ofHom (MvPolynomial.eval₂Hom α a))
  let _ : Etale u := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hα
  have ht : t ≫ P = u := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext b
    exact MvPolynomial.eval₂Hom_C _ _ _
  let _ : Etale G := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  have hcoords : q.comp g =
      ψ.comp (MvPolynomial.eval₂Hom α a) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C] using
        (RingHom.congr_fun hq b).trans (RingHom.congr_fun hψ b).symm
    · intro i
      simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X'] using (ha i).symm
  have hpoint : Spec.map (CommRingCat.ofHom q) ≫ G =
      Spec.map (CommRingCat.ofHom ψ) ≫ t := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k)) hcoords
  let z := EtaleCoordinateSlice.pointLift G t _ _ hpoint
  refine ⟨EtaleCoordinateSlice.space G t, EtaleCoordinateSlice.toBase G t ≫ u,
    EtaleCoordinateSlice.toSource G t, z, inferInstance, ?_, ?_,
    EtaleCoordinateSlice.pointLift_source _ _ _ _ _⟩
  · rw [CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
    change (pullback.fst G t ≫ G) ≫ P = pullback.snd G t ≫ u
    rw [pullback.condition, Category.assoc, ht]
  · rw [← Category.assoc, EtaleCoordinateSlice.pointLift_base, ← Spec.map_comp]
    exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k)) hψ

end FLT.Mazur.EtalePolynomialSeparableLift

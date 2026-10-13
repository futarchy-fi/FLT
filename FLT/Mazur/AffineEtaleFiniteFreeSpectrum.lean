/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeTranslationRefinement
public import FLT.Mazur.AffineEtaleFiniteFaithfulSpectrum

/-!
# Finite faithful translation spectra with actual finite section bases

Compose the finite faithful etale refinement with its constructed finite-free
principal refinement. The original chosen point and neighborhood are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.EtaleTranslationBranch
open Approximation
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] [Algebra.FiniteType ℤ R] {V : Scheme.{u}}
  (g : V ⟶ Spec (.of R)) [IsAffine V] [Etale g]

/-- Each translation point has a finite faithful refinement with a genuine section basis. -/
theorem exists_finite_free_faithful_spectrum (v : V) (U : V.Opens) (hv : v ∈ U) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra.FiniteType ℤ S)
      (a : Spec (.of S) ⟶ Spec (.of R)) (W : Over (Spec (.of S)))
      (_ : IsAffine W.left) (_ : Etale W.hom) (_ : IsFinite W.hom)
      (_ : Surjective W.hom) (t : (Over.map a).obj W ⟶ Over.mk g),
      Etale a ∧ Etale t.left ∧
      (let _ := affineBaseSectionAlgebra W.hom
       ∃ n : ℕ, Nonempty (Basis (Fin n) S Γ(W.left, ⊤))) ∧
      Set.range t.left ⊆ (U : Set V) ∧ ∃ w : W.left, t.left w = v := by
  obtain ⟨T, hT, hRT, hEt, hZ, Z, hZaff, b, s, hb, hs, hfin, hsurj, hsq, hU, z, hz⟩ :=
    exists_finite_faithful_spectrum g v U hv
  let B := Over.mk s
  let _ : IsAffine B.left := hZaff
  let _ : Etale B.hom := hs
  let _ : IsFinite B.hom := hfin
  let _ : Surjective B.hom := hsurj
  obtain ⟨r, _, n, hn, w, hw⟩ := exists_normSource_basis B z
  let _ : Algebra ℤ (Localization.Away r) := Ring.toIntAlgebra _
  let hFT : Algebra.FiniteType ℤ (Localization.Away r) :=
    Algebra.FiniteType.trans (R := ℤ) (S := T) inferInstance inferInstance
  let a₀ := Spec.map (CommRingCat.ofHom (algebraMap R T))
  let _ : Etale a₀ := HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr hEt)
  let a := normBaseMap r ≫ a₀
  let W := Over.mk (normSourceBase B r)
  let t : (Over.map a).obj W ⟶ Over.mk g :=
    Over.homMk (normSourceMap B r ≫ b) (by
      change (normSourceMap B r ≫ b) ≫ g = normSourceBase B r ≫ a
      rw [Category.assoc, hsq, ← Category.assoc]
      change (normSourceMap B r ≫ B.hom) ≫ a₀ = normSourceBase B r ≫ a
      rw [← (normSource_isPullback B r).w, Category.assoc])
  let _ : IsAffine W.left := normSource_affine B r
  let _ : Etale W.hom := normSourceBase_etale B r
  let _ : IsFinite W.hom := normSourceBase_finite B r
  let _ : Surjective W.hom := normSourceBase_surjective B r
  have ht : Etale t.left := by
    change Etale (normSourceMap B r ≫ b)
    infer_instance
  refine ⟨Localization.Away r, inferInstance, hFT, a, W,
    inferInstance, inferInstance, inferInstance, inferInstance, t,
    inferInstance, ht, ⟨n, hn⟩, ?_, w, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact hU ⟨normSourceMap B r q, rfl⟩
  · change b (normSourceMap B r w) = v
    rw [hw, hz]

end FLT.Mazur.EtaleTranslationBranch

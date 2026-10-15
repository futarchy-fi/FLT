/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResidueGeometricConjugacy
public import FLT.Mazur.SmoothInvariantOpenAllEtaleLifts

/-!
# All independent lifts over the original coefficient ring

A finite-orbit nonempty open in an irreducible geometric smooth fiber
constructs an affine étale test of the unchanged coefficient ring. Every
independent geometric lift of this original test satisfies the open
condition. A residue-field preimmersion and algebraic-closure coefficient
field retain the original base throughout the construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalInvariantOpenAllEtaleLifts
open GeometricCoefficientAutomorphisms
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [Algebra k K]
  [IsAlgClosed K] [Algebra.IsAlgebraic k K] {V Y : Scheme}
  (t : Spec (.of k) ⟶ Spec (.of R)) [IsPreimmersion t]
  (f : V ⟶ Spec (.of R)) [Smooth f]
  (a : Y ⟶ V) (b : Y ⟶ Spec (.of K))
  (H : IsPullback a b f (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t))
  [IrreducibleSpace Y] (U : Y.Opens)

/-- The constructed original étale test satisfies the open condition at every independent lift. -/
theorem exists_all_lifts (hne : (U : Set Y).Nonempty)
    (hf : (Set.range (fun σ : K ≃ₐ[k] K ↦
      (ResidueGeometricConjugacy.fiberAction t H σ).hom ⁻¹' (U : Set Y))).Finite) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ V)
      (z : Spec (.of K) ⟶ E), IsAffine E ∧ Etale e ∧ v ≫ f = e ∧
      z ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t ∧
      ∀ w : Spec (.of K) ⟶ E,
        w ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t →
        ∃ u : Spec (.of K) ⟶ U.toScheme,
          u ≫ U.ι ≫ b = 𝟙 _ ∧ w ≫ v = u ≫ U.ι ≫ a := by
  obtain ⟨E, e, v, z, w, hE, he, hv, hz, hwb, hwa, horbit⟩ :=
    SchemeFiniteOrbitOpenCore.exists_etale_orbit_lift
      (ResidueGeometricConjugacy.fiberAction t H) U hf
      f _ a b H hne
  let _ : Etale e := he
  let _ : IsAffine E := hE
  let _ : LocallyQuasiFinite e := by
    apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite)).mpr
    let _ := e.appTop.hom.toAlgebra
    let _ : Algebra.Etale Γ(Spec (.of R), ⊤) Γ(E, ⊤) :=
      HasRingHomProperty.appTop (P := @Etale) e he
    exact inferInstanceAs (Algebra.QuasiFinite Γ(Spec (.of R), ⊤) Γ(E, ⊤))
  obtain ⟨A, q, z', hA, hq, hzq, hsingle⟩ :=
    QuasiFiniteGeometricPointIsolation.exists_affine_geometric_factor e z
  let _ : IsOpenImmersion q := hq
  refine ⟨A, q ≫ e, q ≫ v, z', hA, inferInstance, ?_, ?_, fun l hl ↦ ?_⟩
  · rw [Category.assoc, hv]
  · rw [← Category.assoc, hzq, hz]
  · have hle : (l ≫ q) ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t := by
      simpa only [Category.assoc] using hl
    have hp : (l ≫ q) default = z default := hsingle l (hl.trans hz.symm)
    obtain ⟨σ, hσ⟩ := ResidueGeometricConjugacy.exists_conjugacy t e
      z (l ≫ q) hz hle hp.symm
    change (specAction σ).inv ≫ z = l ≫ q at hσ
    obtain ⟨u, hu⟩ := horbit σ
    refine ⟨(specAction σ).inv ≫ u, ?_, ?_⟩
    · rw [Category.assoc, ← Category.assoc u, hu, Category.assoc]
      rw [ResidueGeometricConjugacy.fiberAction_snd, ← Category.assoc w,
        hwb, Category.id_comp, Iso.inv_hom_id]
    · rw [Category.assoc, ← Category.assoc u, hu, Category.assoc,
        ResidueGeometricConjugacy.fiberAction_fst]
      rw [← hwa, ← Category.assoc (specAction σ).inv z v, hσ, Category.assoc]

end FLT.Mazur.OriginalInvariantOpenAllEtaleLifts

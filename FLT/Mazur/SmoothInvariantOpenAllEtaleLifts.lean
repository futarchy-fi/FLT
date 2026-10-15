/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricCoefficientAutomorphisms
public import FLT.Mazur.GeometricResidueMorphismConjugacy
public import FLT.Mazur.QuasiFiniteGeometricPointIsolation
public import FLT.Mazur.SchemeFiniteOrbitOpenCore
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Every independent étale lift meets a finite-orbit geometric open

For an irreducible smooth geometric fiber over an algebraic closure, a
nonempty open with finite coefficient orbit constructs an original affine
étale test. Every independent geometric lift of this test meets the open,
with its whole original morphism retained. The test and its refinement are
outputs; no branch enumeration or selected-base-map condition is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothInvariantOpenAllEtaleLifts
open GeometricCoefficientAutomorphisms
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed K] [Algebra.IsAlgebraic k K] {V Y : Scheme}
  (f : V ⟶ Spec (.of k)) [Smooth f]
  (a : Y ⟶ V) (b : Y ⟶ Spec (.of K))
  (H : IsPullback a b f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  [IrreducibleSpace Y] (U : Y.Opens)

/-- The constructed original étale test satisfies the open condition at every independent lift. -/
theorem exists_all_lifts (hne : (U : Set Y).Nonempty)
    (hf : (Set.range (fun σ : K ≃ₐ[k] K ↦
      (fiberAction H σ).hom ⁻¹' (U : Set Y))).Finite) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of k)) (v : E ⟶ V)
      (z : Spec (.of K) ⟶ E), IsAffine E ∧ Etale e ∧ v ≫ f = e ∧
      z ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) ∧
      ∀ w : Spec (.of K) ⟶ E,
        w ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) →
        ∃ u : Spec (.of K) ⟶ U.toScheme,
          u ≫ U.ι ≫ b = 𝟙 _ ∧ w ≫ v = u ≫ U.ι ≫ a := by
  obtain ⟨E, e, v, z, w, hE, he, hv, hz, hwb, hwa, horbit⟩ :=
    SchemeFiniteOrbitOpenCore.exists_etale_orbit_lift (fiberAction H) U hf
      f _ a b H hne
  let _ : Etale e := he
  let _ : IsAffine E := hE
  let _ : LocallyQuasiFinite e := by
    apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite)).mpr
    let _ := e.appTop.hom.toAlgebra
    let _ : Algebra.Etale Γ(Spec (.of k), ⊤) Γ(E, ⊤) :=
      HasRingHomProperty.appTop (P := @Etale) e he
    exact inferInstanceAs (Algebra.QuasiFinite Γ(Spec (.of k), ⊤) Γ(E, ⊤))
  obtain ⟨A, q, z', hA, hq, hzq, hsingle⟩ :=
    QuasiFiniteGeometricPointIsolation.exists_affine_geometric_factor e z
  let _ : IsOpenImmersion q := hq
  refine ⟨A, q ≫ e, q ≫ v, z', hA, inferInstance, ?_, ?_, fun l hl ↦ ?_⟩
  · rw [Category.assoc, hv]
  · rw [← Category.assoc, hzq, hz]
  · have hle : (l ≫ q) ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      simpa only [Category.assoc] using hl
    have hp : (l ≫ q) default = z default := hsingle l (hl.trans hz.symm)
    obtain ⟨σ, hσ⟩ := GeometricResidueMorphismConjugacy.exists_conjugacy e
      z (l ≫ q) hz hle hp.symm
    change (specAction σ).inv ≫ z = l ≫ q at hσ
    obtain ⟨u, hu⟩ := horbit σ
    refine ⟨(specAction σ).inv ≫ u, ?_, ?_⟩
    · rw [Category.assoc, ← Category.assoc u, hu, Category.assoc]
      exact normalized_conjugate_base H w hwb σ
    · rw [Category.assoc, ← Category.assoc u, hu, Category.assoc, fiberAction_fst]
      rw [← hwa, ← Category.assoc (specAction σ).inv z v, hσ, Category.assoc]

end FLT.Mazur.SmoothInvariantOpenAllEtaleLifts

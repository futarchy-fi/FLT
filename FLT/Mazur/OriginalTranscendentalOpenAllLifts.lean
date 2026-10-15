/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalSmoothDetectingEtaleLift
public import FLT.Mazur.OriginalTranscendentalResidueConjugacy
public import FLT.Mazur.QuasiFiniteUniversalPointIsolation
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Original étale neighborhoods controlling every independent K-lift

The larger field need not be algebraic over the original residue field.
Choose the smooth étale point inside the algebraic detecting open, isolate
its original support, and use whole-morphism conjugacy for every K-lift.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalTranscendentalOpenAllLifts
set_option backward.isDefEq.respectTransparency false
variable {R k L K : Type} [CommRing R] [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [IsAlgClosed L] {V X Y : Scheme}

include L

/-- Every independent larger-field lift of a constructed original test satisfies all opens. -/
theorem exists_all_lifts (f : V ⟶ Spec (.of R)) [Smooth f]
    (t : Spec (.of k) ⟶ Spec (.of R)) [IsPreimmersion t]
    (x : X ⟶ V) (g : X ⟶ Spec (.of k)) (H₀ : IsPullback x g f t)
    [GeometricallyIntegral g] (a : Y ⟶ Spec (.of K)) (b : Y ⟶ X)
    (H : IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap k K))) g)
    {J : Type*} [Finite J] (U : J → Y.Opens) (hU : ∀ j, (U j : Set Y).Nonempty) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ V)
      (z : Spec (.of K) ⟶ E), IsAffine E ∧ Etale e ∧ v ≫ f = e ∧
      z ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t ∧
      ∀ w : Spec (.of K) ⟶ E,
        w ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t →
        ∃ u : Spec (.of K) ⟶ Y, u ≫ a = 𝟙 _ ∧
          w ≫ v = u ≫ b ≫ x ∧ ∀ j, Set.range u ⊆ U j := by
  obtain ⟨E, e, v, z, q, hE, he, hv, hz, hq, hqv, hqU⟩ :=
    OriginalSmoothDetectingEtaleLift.exists_lift (L := L) f t x g H₀ a b H U hU
  let _ : Etale e := he
  let _ : IsAffine E := hE
  let _ : LocallyQuasiFinite e := by
    apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite)).mpr
    let _ := e.appTop.hom.toAlgebra
    let _ : Algebra.Etale Γ(Spec (.of R), ⊤) Γ(E, ⊤) :=
      HasRingHomProperty.appTop (P := @Etale) e he
    exact inferInstanceAs (Algebra.QuasiFinite Γ(Spec (.of R), ⊤) Γ(E, ⊤))
  obtain ⟨A, i, z', hA, hi, hzi, hsingle⟩ :=
    QuasiFiniteUniversalPointIsolation.exists_factor e z
  let _ : IsOpenImmersion i := hi
  let c := Spec.map (CommRingCat.ofHom (algebraMap L K))
  have hc : c ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact (IsScalarTower.algebraMap_apply k L K r).symm
  refine ⟨A, i ≫ e, i ≫ v, c ≫ z', hA, inferInstance, ?_, ?_, fun w hw ↦ ?_⟩
  · rw [Category.assoc, hv]
  · rw [Category.assoc, ← Category.assoc z', hzi, hz, ← Category.assoc, hc]
  · have hwe : (w ≫ i) ≫ e = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t := by
      simpa only [Category.assoc] using hw
    have hs : e (i (w default)) = e (z default) := by
      change ((w ≫ i) ≫ e) default = (z ≫ e) default
      rw [hwe, hz]
      change t _ = t _
      exact congrArg t (Subsingleton.elim _ _)
    have hp : z default = (w ≫ i) default := (hsingle (w default) hs).symm
    obtain ⟨σ, hσ⟩ := OriginalTranscendentalResidueConjugacy.exists_conjugacy
      t e z (w ≫ i) hz hwe hp
    refine ⟨q σ, hq σ, ?_, hqU σ⟩
    rw [hqv σ]
    have h := congrArg (fun l : Spec (.of K) ⟶ E ↦ l ≫ v) hσ
    simpa only [Category.assoc] using h.symm

end FLT.Mazur.OriginalTranscendentalOpenAllLifts

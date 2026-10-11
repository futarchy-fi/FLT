/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSmoothEtaleCoordinates
public import FLT.Mazur.EtalePolynomialSeparableLift

/-!
# Smooth étale local sections through separable residue points

Points over separable extensions of a base residue field extend to actual
étale neighborhoods of the original base. The construction preserves their
field-valued maps and gives sections of the actual base-changed smooth source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothEtaleSeparableLift
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] {X : Scheme}

/-- A smooth separable residue point extends to a constructed étale base neighborhood. -/
theorem exists_lift (f : X ⟶ Spec (.of R)) [Smooth f]
    (φ : R →+* k) (hφ : φ.SurjectiveOnStalks) (x : Spec (.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ X) (z : Spec (.of K) ⟶ E),
      Etale e ∧ v ≫ f = e ∧
        z ≫ e = Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)) ∧ z ≫ v = x := by
  obtain ⟨A, n, g, j, hg, hj, hy, hf⟩ :=
    AffineSmoothEtaleCoordinates.exists_chart f (x (IsLocalRing.closedPoint K))
  let _ := hj
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    simpa only [Subsingleton.elim w (IsLocalRing.closedPoint K)] using hy
  let a := IsOpenImmersion.lift j x hr
  have ha : a ≫ j = x := IsOpenImmersion.lift_fac j x hr
  obtain ⟨q, hq⟩ := Spec.map_surjective a
  have hbase : Spec.map q ≫ Spec.map (CommRingCat.ofHom g) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) =
        Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)) := by
    rw [hq, ← hf, ← Category.assoc, ha, hx]
  have hring : q.hom.comp (g.comp MvPolynomial.C) = (algebraMap k K).comp φ := by
    rw [← Spec.map_comp, ← Spec.map_comp] at hbase
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hbase)
  obtain ⟨E, e, v, z, he, hv, hz, hvz⟩ :=
    EtalePolynomialSeparableLift.exists_lift g hg q.hom φ hφ hring
      (fun i ↦ Algebra.IsSeparable.isSeparable k (q.hom (g (MvPolynomial.X i))))
  refine ⟨E, e, v ≫ j, z, he, ?_, hz, ?_⟩
  · rw [Category.assoc, hf, ← Spec.map_comp]
    exact hv
  · rw [← Category.assoc, hvz]
    exact (congrArg (fun k ↦ k ≫ j) hq).trans ha

/-- The neighborhood gives a section of the actual base-changed smooth source through the point. -/
theorem exists_section (f : X ⟶ Spec (.of R)) [Smooth f]
    (φ : R →+* k) (hφ : φ.SurjectiveOnStalks) (x : Spec (.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (z : Spec (.of K) ⟶ E)
      (s : E ⟶ pullback f e),
      Etale e ∧ s ≫ pullback.snd f e = 𝟙 E ∧
        z ≫ e = Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)) ∧
          z ≫ s ≫ pullback.fst f e = x := by
  obtain ⟨E, e, v, z, he, hv, hz, hvz⟩ := exists_lift f φ hφ x hx
  refine ⟨E, e, z, pullback.lift v (𝟙 E) (by simpa only [Category.id_comp] using hv),
    he, pullback.lift_snd _ _ _, hz, ?_⟩
  rw [pullback.lift_fst, hvz]

/-- Every separable extension of any base residue field admits this local-section construction. -/
theorem exists_residue_section (f : X ⟶ Spec (.of R)) [Smooth f]
    (p : Ideal R) [p.IsPrime] [Algebra p.ResidueField K]
    [Algebra.IsSeparable p.ResidueField K] (x : Spec (.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom
      ((algebraMap p.ResidueField K).comp (algebraMap R p.ResidueField)))) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (z : Spec (.of K) ⟶ E)
      (s : E ⟶ pullback f e),
      Etale e ∧ s ≫ pullback.snd f e = 𝟙 E ∧
        z ≫ e = Spec.map (CommRingCat.ofHom
          ((algebraMap p.ResidueField K).comp (algebraMap R p.ResidueField))) ∧
          z ≫ s ≫ pullback.fst f e = x :=
  exists_section f _ p.surjectiveOnStalks_residueField x hx

end FLT.Mazur.SmoothEtaleSeparableLift

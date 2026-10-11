/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtalePolynomialSeparablePointDescent
public import FLT.Mazur.SeparableAffineOpenPoints
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Separable representatives in every geometric open of an étale chart

Base change an original étale polynomial chart to a geometric coefficient
field. Every nonempty open contains a field-valued point whose projection to
the original chart descends to the relative separable closure. The selected
point remains inside the specified geometric open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtalePolynomialGeometricOpenPoints
set_option backward.isDefEq.respectTransparency false
variable {k K B : Type} [Field k] [Field K] [IsSepClosed K] [Algebra k K] [CommRing B]
  {n : ℕ}

/-- The coefficient extension on the original affine coordinate space. -/
def coefficientMap : Spec (.of (MvPolynomial (Fin n) K)) ⟶
    Spec (.of (MvPolynomial (Fin n) k)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap k K)))

/-- The actual geometric base change of the original étale polynomial chart. -/
def space (g : MvPolynomial (Fin n) k →+* B) : Scheme :=
  pullback (Spec.map (CommRingCat.ofHom g)) (coefficientMap (K := K))

/-- Nonempty geometric opens contain points descending to separable original coefficients. -/
theorem exists_point (g : MvPolynomial (Fin n) k →+* B) (hg : g.Etale)
    (W : Set (space (K := K) g)) (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (q₀ : B →+* separableClosure k K) (z : Spec (.of K) ⟶ space (K := K) g),
      z default ∈ W ∧ z ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom ((algebraMap (separableClosure k K) K).comp q₀)) := by
  let G := Spec.map (CommRingCat.ofHom g)
  let c := coefficientMap (k := k) (K := K) (n := n)
  let e := pullback.snd G c
  let _ : Etale G := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  have himage : IsOpen (e '' W) := e.isOpenMap W hW
  obtain ⟨v, hv, hvW⟩ := SeparableAffineOpenPoints.exists_point (k := k)
    (e '' W) himage (hne.image e)
  obtain ⟨w, hw, hew⟩ := hvW
  let t := Spec.map (CommRingCat.ofHom (MvPolynomial.eval v))
  have hpoint : e w = t default := by
    rw [hew]
    simp only [t, Spec.map_apply, SeparableAffineOpenPoints.point]
    congr 1
  obtain ⟨z, hz, hzw⟩ := Scheme.exists_fac_of_etale_of_isSepClosed e t w hpoint
  obtain ⟨q, hq⟩ := Spec.map_surjective (z ≫ pullback.fst G c)
  have hcoords : q.hom.comp g =
      (MvPolynomial.eval v).comp (MvPolynomial.map (algebraMap k K)) := by
    have h : Spec.map q ≫ G = t ≫ c := by
      rw [hq, Category.assoc, pullback.condition, ← Category.assoc, hz]
    dsimp only [G, t, c, coefficientMap] at h
    rw [← Spec.map_comp, ← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have hbase : q.hom.comp (g.comp MvPolynomial.C) = algebraMap k K := by
    ext r
    simpa only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval_C]
      using RingHom.congr_fun hcoords (MvPolynomial.C r)
  have hsep (i : Fin n) : IsSeparable k (q.hom (g (MvPolynomial.X i))) := by
    have h := RingHom.congr_fun hcoords (MvPolynomial.X i)
    simp only [RingHom.comp_apply, MvPolynomial.map_X, MvPolynomial.eval_X] at h
    rw [h]
    exact hv i
  obtain ⟨q₀, hq₀⟩ := EtalePolynomialSeparablePointDescent.exists_factor g hg q.hom hbase hsep
  refine ⟨q₀, z, hzw.symm ▸ hw, ?_⟩
  rw [hq₀]
  exact hq.symm

end FLT.Mazur.EtalePolynomialGeometricOpenPoints

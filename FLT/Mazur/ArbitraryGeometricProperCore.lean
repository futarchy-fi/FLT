/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricAffineFullFiber
public import FLT.Mazur.EtaleWholeFiberProperNeighborhood

/-!
# Constructed proper cores through arbitrary original proper-family classes

Construct the original affine full-fiber chart, then a common affine etale
ground with a finite clopen translation core containing its whole distinguished
fiber. The original geometric source morphism lifts exactly to that ground.
The ambient changed translation remains the full Cartesian pullback; the
finite core does not replace it or discard its independent residual points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))
local notation "η" => (default : Spec (CommRingCat.of K))

include hL in
/-- An arbitrary original class has a common-ground proper core containing every fiber branch. -/
theorem exists_arbitrary_geometric_proper_core
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A), IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left, let _ := hk
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s ∧
      b.left η ∈ fullEnvelopeLocus f hL d V c k ∧
      ∃ (U : Scheme) (q : U ⟶ Spec (.of R)) (z : Spec (.of K) ⟶ U),
        IsAffine U ∧ Etale q ∧ z ≫ q = t ∧
        ∃ T : (pullback V.hom q).Opens,
          IsClosed (T : Set (pullback V.hom q : Scheme)) ∧
          IsFinite (T.ι ≫ pullback.snd V.hom q) ∧
          Etale (T.ι ≫ pullback.snd V.hom q) ∧ IsAffine T.toScheme ∧
          T ≤ ProperNeighborhoodAtlas.locus (pullback.snd V.hom q) ∧
          (∀ y : (pullback V.hom q : Scheme),
            pullback.snd V.hom q y = z η → y ∈ T) ∧
          ∃ β : Spec (.of K) ⟶ pullback A.hom q,
            β ≫ pullback.fst A.hom q = b.left ∧
            β ≫ pullback.snd A.hom q = z ∧ IsOpenMap (pullback.fst A.hom q) := by
  obtain ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx⟩ :=
    exists_arbitrary_geometric_affine_full_fiber f hL t s
  let _ := hV
  let _ := he
  obtain ⟨U, q, z, hU, hq, hz, T, hTclosed, hf, hTale, hTaff, hT, ht⟩ :=
    EtaleWholeFiberProperNeighborhood.exists_finite_open V.hom t
  let _ := hq
  let β := pullback.lift b.left z (b.w.trans hz.symm)
  exact ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx,
    U, q, z, hU, hq, hz, T, hTclosed, hf, hTale, hTaff, hT, ht,
    β, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
    (pullback.fst A.hom q).isOpenMap⟩

end FLT.Mazur.HilbertChart.AffineRestriction

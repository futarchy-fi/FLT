/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricProperCore
public import FLT.Mazur.CommonGroundResidualGenerizations
public import FLT.Mazur.VariableHilbertNoetherianSource

/-!
# Full Cartesian envelope cores through arbitrary proper-family classes

Assemble the actual common-ground envelope square and its finite clopen core
for the constructed original affine Hilbert chart. The whole original class
map lifts, and the exact obstruction concerns the original full interior.
A finite family of actual residual generic points tests the original interior.
Avoidance of the residual image is proved; avoidance of its closure is not.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve CommonGroundEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))
local notation "η" => (default : Spec (CommRingCat.of K))

include hL in
/-- Construct the actual finite independent core and identify its exact original obstruction. -/
theorem exists_arbitrary_geometric_envelope_core
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
        ∃ (T : (pullback V.hom q).Opens) (β : Spec (.of K) ⟶ pullback A.hom q),
          β ≫ pullback.fst A.hom q = b.left ∧ β ≫ pullback.snd A.hom q = z ∧
          IsFinite (T.ι ≫ pullback.snd V.hom q) ∧
          let B := changed q A
          let W := changed q V
          let π := (prod.fst : prod B W ⟶ B).left
          let O := (toEnvelope f hL d V c k).left.opensRange
          IsPullback (comparison q A V) π (prod.fst : prod A V ⟶ A).left
            (pullback.fst A.hom q) ∧
          IsFinite ((envelopeCore q A V T).ι ≫ π) ∧
          IsClosed (envelopeCore q A V T : Set (prod B W).left) ∧
          (∀ e : (prod B W).left, π e = β η → e ∈ envelopeCore q A V T) ∧
          β η ∉ residualImage q A V T O ∧
          (b.left η ∈ fullEnvelopeInterior f hL d V c k ↔
            β η ∉ closure (residualImage q A V T O)) ∧
          ∃ F : Set (prod B W).left, F.Finite ∧
            (∀ e ∈ F, comparison q A V e ∉ O ∧ e ∉ envelopeCore q A V T) ∧
            (∀ e ∈ F, π e ≠ β η) ∧
            (b.left η ∈ fullEnvelopeInterior f hL d V c k ↔
              ∀ e ∈ F, ¬ π e ⤳ β η) := by
  obtain ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx,
    U, q, z, hU, hq, hz, T, hTc, hf, _, _, _, ht, β, hβ, hβz, _⟩ :=
    exists_arbitrary_geometric_proper_core f hL t s
  let _ := hk
  let _ := hV
  let _ := he
  let _ := hA
  let _ := hU
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := hq
  let _ := hf
  have hpoint : pullback.fst A.hom q (β η) = b.left η :=
    congrArg (fun m : Spec (.of K) ⟶ A.left ↦ m η) hβ
  have hground : pullback.snd A.hom q (β η) = z η :=
    congrArg (fun m : Spec (.of K) ⟶ U ↦ m η) hβz
  refine ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx, U, q, z, hU, hq, hz,
    T, β, hβ, hβz, hf, CommonGroundEnvelope.isPullback q A V, inferInstance,
    envelopeCore_isClosed q A V T hTc,
    fiber_subset_envelopeCore q A V T (z η) ht (β η) hground,
    not_mem_residualImage q A V T _ (z η) ht (β η) hground, ?_, ?_⟩
  · have hi := original_interior_iff q A V T
      (toEnvelope f hL d V c k).left.opensRange (β η) (by rwa [hpoint])
    rwa [hpoint] at hi
  · obtain ⟨F, hF, hFO, htest⟩ := exists_finite_originalInterior_test q A V T
      (toEnvelope f hL d V c k).left.opensRange
    refine ⟨F, hF, hFO, ?_, ?_⟩
    · intro e heq hp
      exact (hFO e heq).2
        (fiber_subset_envelopeCore q A V T (z η) ht (β η) hground e hp)
    · have hi := htest (β η) (by rwa [hpoint])
      rwa [hpoint] at hi

end FLT.Mazur.HilbertChart.AffineRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricAffineFullFiber
public import FLT.Mazur.ArtinianHilbertFullInterior

/-!
# Original full-interior charts through arbitrary classes over Artinian ground

Start with an arbitrary proper-family Picard class. Construct its original
affine full-fiber chart and prove original interior membership using the actual
Artinian coefficient scheme. Lift the whole geometric test to the resulting
invariant open and recover its original section. The new open is not asserted
affine, and no global quotient scheme over general coefficients is claimed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  [IsLocallyArtinian (Spec (.of R))] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))
local notation "η" => (default : Spec (CommRingCat.of K))

include hL in
/-- Arbitrary classes have constructed original full-interior charts on Artinian ground. -/
theorem exists_arbitrary_geometric_artinian_interior
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A), IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left, let _ := hk
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s ∧
      b.left η ∈ fullEnvelopeInterior f hL d V c k ∧
      ∃ z : Over.mk t ⟶ fullInteriorSource f hL d V c k,
        z ≫ fullInteriorSourceMap f hL d V c k = b ∧
        (relativeFppfSheaf f).obj.map z.op
          (sectionAt f hL d V c (fullInteriorChart f hL d V c k)) = s ∧
        ∃ r : compatibleFunctions
            (fst f hL d V c (fullInteriorChart f hL d V c k)).left
            (snd f hL d V c (fullInteriorChart f hL d V c k)).left,
          r ∈ invariantEnvelopeDenominators f hL d V c (fullInteriorChart f hL d V c k) ∧
          z.left η ∈ (fullInteriorSource f hL d V c k).left.basicOpen r.val := by
  obtain ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx⟩ :=
    exists_arbitrary_geometric_affine_full_fiber f hL t s
  let _ := hV
  let _ := he
  let _ := hk
  have hi : b.left η ∈ fullEnvelopeInterior f hL d V c k := by
    rw [← SetLike.mem_coe, artinian_fullEnvelopeInterior_coe]
    exact hx
  have hr : Set.range b.left ⊆ fullEnvelopeLocus f hL d V c k := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of K)) x η]
    exact hx
  let z := artinianFullInteriorLift f hL d V c k b hr
  refine ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hi, z,
    artinianFullInteriorLift_comp f hL d V c k b hr, ?_, ?_⟩
  · exact (artinianFullInteriorLift_section f hL d V c k b hr).trans hb
  · exact fullInteriorChart_nonvanishing f hL d V c k (z.left η)

end FLT.Mazur.HilbertChart.AffineRestriction

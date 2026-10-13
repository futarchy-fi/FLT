/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormOrbitFiber
public import FLT.Mazur.AffineHilbertFullFiberRestriction

/-!
# Norm support inside a restricted full Hilbert interior

If a source section is supported inside an open restriction, its norm's
nonzero locus retains all original orbit endpoints. The entire independent
fiber survives, so this open lies in the new chart's full-fiber interior.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] [IsIso (toEnvelope f hL d V c k).left]
  {B : Over (Spec (.of R))} (v : B ⟶ A) [IsOpenImmersion v.left]
/-- The original translation structural algebra. -/
local instance nestedNormTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
  (s : Γ(A.left, ⊤)) (hs : A.left.basicOpen s ≤ v.left.opensRange)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

include hs
/-- Every nonzero restricted norm point retains its full original independent fiber. -/
theorem nestedNorm_fullFiber (x : B.left)
    (hx : x ∈ B.left.basicOpen (v.left.appTop
      (fullEnvelopeRegularNorm f hL d V c k b s))) :
    x ∈ fullEnvelopeLocus f hL d V c (v ≫ k) := by
  rw [← Scheme.preimage_basicOpen_top] at hx
  have ho := (mem_basicOpen_fullEnvelopeNorm_iff f hL d V c k b s (v.left x)).mp hx
  apply nested_fullFiber_retained f hL d V c k v x
  · apply (mem_fullFiberLocus _ _ _).mpr
    intro y _
    exact (toEnvelope f hL d V c k).left.homeomorph.surjective y
  · intro z hz
    exact hs (ho z hz)

/-- The actual nonzero norm open is supported in the NEW full-fiber interior. -/
theorem nestedNorm_basicOpen_le_fullInterior :
    B.left.basicOpen (v.left.appTop (fullEnvelopeRegularNorm f hL d V c k b s)) ≤
      fullEnvelopeInterior f hL d V c (v ≫ k) := by
  apply interior_maximal _ (B.left.basicOpen _).isOpen
  intro x hx
  exact nestedNorm_fullFiber f hL d V c k v b s hs x hx

end FLT.Mazur.HilbertChart.AffineRestriction

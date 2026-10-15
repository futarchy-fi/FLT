/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.JointGroundNormInvariantOpen
public import FLT.Mazur.HilbertEnvelopeSourceTransport
public import FLT.Mazur.AffineHilbertNestedRestriction

/-!
# Joint finite subchart norms preserve the full original Hilbert relation

The original full-envelope source section supplies the transport equation.
Joint coverage suffices for invariance of the product norm's open, even if the
individual finite subcharts cannot be transported across independent grounds.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeTranslationNorm
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd toEnvelope
variable {R S : Type} [CommRing R] [CommRing S] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (w : (Over.map a).obj W ⟶ V) (H : IsPullback w.left W.hom V.hom a)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsIso (toEnvelope f hL d V c k).left] {B : Over (Spec (.of S))}
  (u : (Over.map a).obj B ⟶ A)
  {I : Type} [Fintype I] (T : I → Over (Spec (.of S))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- Each chart supplies its own finite translation algebra, without a basis on the old ground. -/
local instance hilbertJointNormTranslationAlgebra (i : I) : Algebra S Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) S Γ((T i).left, ⊤))
  (ht : ∀ z : W.left, ∃ i, ∃ y : (T i).left, (t i).left y = z)
  (s : Γ(A.left, ⊤))
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "r" => fst f hL d V c (u ≫ k)
local notation "v" => snd f hL d V c (u ≫ k)
local notation "z" => nestedToFullRelation f hL d V c k u

/-- The actual product of norms of the original source section on all finite subcharts. -/
def hilbertJointGroundNorm : Γ(B.left, ⊤) :=
  jointTranslationNorm B W T t b ((fixedBaseEnvelopeMap a V W w u).left.appTop
    (fullEnvelopeSourceSection f hL d V c k s))

include H ht

/-- The FULL original relation preserves the open, including arrows with different new grounds. -/
theorem hilbertJointGroundNorm_open_invariant :
    (r).left ⁻¹ᵁ B.left.basicOpen (hilbertJointGroundNorm f hL d a V W w c k u T t b s) =
      (v).left ⁻¹ᵁ B.left.basicOpen (hilbertJointGroundNorm f hL d a V W w c k u T t b s) := by
  exact jointGroundNorm_open_transport V p q (fullEnvelopeSourceSection f hL d V c k s)
    (fullEnvelopeSourceSection_transport f hL d V c k s)
    a W w H u T t b ht (r).left (v).left (z).left
    (congrArg Over.Hom.left (nestedToFullRelation_fst f hL d V c k u))
    (congrArg Over.Hom.left (nestedToFullRelation_snd f hL d V c k u))

/-- The invariant open keeps the exact original full-fiber support after an open source change. -/
theorem hilbertJointGroundNorm_fullInterior (hu : IsOpenMap u.left) :
    B.left.basicOpen (hilbertJointGroundNorm f hL d a V W w c k u T t b s) =
      u.left ⁻¹ᵁ SchemeOpenEnvelope.fullFiberInterior (prod.fst : prod A V ⟶ A).left
        ((prod A V).left.basicOpen (fullEnvelopeSourceSection f hL d V c k s)) :=
  basicOpen_jointGroundNorm_fullInterior a V W w H u T t b ht
    (fullEnvelopeSourceSection f hL d V c k s) hu

end FLT.Mazur.HilbertChart.AffineRestriction

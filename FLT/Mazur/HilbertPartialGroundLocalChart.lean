/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PartialGroundLocalInterior
public import FLT.Mazur.AffineHilbertEnvelopeFiberCount
public import FLT.Mazur.AffineHilbertFullInteriorChart

/-!
# Local original Hilbert neighborhoods from partial ground charts

Only pointwise lifts through an open source comparison are needed. Whole
scheme tests in its image factor uniquely into the original full-interior
chart even without a whole scheme lift to the changed source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeTranslationNorm
open SchemeEffectiveEpiSections
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
  [IsOpenImmersion k.left] {B : Over (Spec (.of S))}
  (u : (Over.map a).obj B ⟶ A) (hu : IsOpenMap u.left)
  {I : Type} [Finite I] (T : I → Over (Spec (.of S))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- Finite bases are needed only for the partial translation charts. -/
local instance hilbertPartialLocalTranslationAlgebra (i : I) : Algebra S Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) S Γ((T i).left, ⊤))
  (ht : ∀ y : (prod B W).left,
    (fixedBaseEnvelopeMap a V W w u).left y ∉ (toEnvelope f hL d V c k).left.opensRange →
      ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y)
local notation "U" => fullEnvelopeInterior f hL d V c k
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)

include H hu b ht

/-- One independent ground lift places an original full fiber in the actual source interior. -/
theorem fullEnvelopeInterior_of_partialGroundLift (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) (hxlift : x ∈ Set.range u.left) : x ∈ U :=
  mem_originalFullInterior_of_partialGroundLift
    a V W w H u hu T t b (j).opensRange ht x hx hxlift

/-- Actual original arrow witnesses and one ground lift construct an original open neighborhood. -/
theorem fullEnvelopeInterior_of_partialGround_lift_witnesses
    [Etale V.hom] [IsAffine V.left] (x : A.left) (hxlift : x ∈ Set.range u.left)
    {n : ℕ} (e : Fin n → (relation f hL d V c k).left) (he : Function.Injective e)
    (hq : ∀ i, (snd f hL d V c k).left (e i) = x)
    (hn : ((prod.fst : prod A V ⟶ A).left ⁻¹' {x}).ncard ≤ n) : x ∈ U :=
  fullEnvelopeInterior_of_partialGroundLift f hL d a V W w H c k u hu T t b ht x
    (fullEnvelopeLocus_of_fiber_witnesses f hL d V c k x e he hq hn) hxlift

variable {Z : Scheme} (g : Z ⟶ A.left)
  (hg : Set.range g ⊆ fullEnvelopeLocus f hL d V c k)
  (hglift : Set.range g ⊆ Set.range u.left)

/-- Pointwise reachability suffices to lift the whole original test into its actual open chart. -/
def localPartialGroundFullInteriorLift : Z ⟶ (fullInteriorSource f hL d V c k).left := by
  change Z ⟶ (U).toScheme
  apply IsOpenImmersion.lift (U).ι g
  rw [Scheme.Opens.range_ι]
  intro x hx
  exact fullEnvelopeInterior_of_partialGroundLift f hL d a V W w H c k u hu T t b ht x
    (hg hx) (hglift hx)

/-- The original scheme map is retained exactly, with all coefficient and nilpotent data. -/
@[reassoc]
theorem localPartialGroundFullInteriorLift_comp :
    localPartialGroundFullInteriorLift f hL d a V W w H c k u hu T t b ht g hg hglift ≫
      (fullInteriorSourceMap f hL d V c k).left = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- No choice of pointwise ground lifts changes the resulting original chart morphism. -/
theorem localPartialGroundFullInteriorLift_unique
    (l : Z ⟶ (fullInteriorSource f hL d V c k).left)
    (hl : l ≫ (fullInteriorSourceMap f hL d V c k).left = g) :
    l = localPartialGroundFullInteriorLift f hL d a V W w H c k u hu T t b ht g hg hglift := by
  apply (cancel_mono (U).ι).mp
  exact hl.trans
    (localPartialGroundFullInteriorLift_comp
      f hL d a V W w H c k u hu T t b ht g hg hglift).symm

end FLT.Mazur.HilbertChart.AffineRestriction

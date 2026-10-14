/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelEtale
public import FLT.Mazur.AffineHilbertFiniteModelEtaleCertificates
public import FLT.Mazur.KernelPairEffectiveEtaleBranch

/-!
# Represented Picard nonemptiness from unrestricted etale source branches

Generic etale certificates for the original full kernel and one nonempty
etale branch of the unrestricted source projection construct an actual point
of the represented original Picard region. The original projection is neither
assumed flat nor assumed unramified. Irreducible targets may be nonreduced.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)

omit [IsAffine A.left] in
/-- One unrestricted etale branch reaches the represented region on an irreducible model. -/
theorem modelFppfTarget_nonempty_of_etale_branch {T : Over (Spec (.of R))}
    (w : A ⟶ T) (hw : p ≫ w.left = q ≫ w.left)
    [LocallyOfFinitePresentation w.left] [IrreducibleSpace T.left]
    {Z : Scheme} (a : Z ⟶ A.left) [Etale (a ≫ w.left)] [Nonempty Z]
    (hE : Nonempty (modelEffectiveTarget f hL d V c k w hw).left) :
    Nonempty (modelFppfTarget f hL d V c k w hw).left := by
  let _ : Mono (pullback.lift p q hw) := modelRelationKernelMap_mono f hL d V c k w.left hw
  obtain ⟨x⟩ := hE
  obtain ⟨y, hy⟩ := KernelPairEffectiveOpen.fppfLocus_nonempty_of_etale_branch
    p q w.left hw a ⟨x.val, x.property⟩
  exact ⟨⟨y, hy⟩⟩

local notation "v" => finiteKernelProjection f hL d V c k
local notation "H" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "K" => (pullback (Over.Hom.left v) (Over.Hom.left v) : Scheme)
local notation "b" => pullback.fst (Over.Hom.left v) (Over.Hom.left v) ≫ (Over.Hom.left v)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "D" => (Over.left (relation f hL d V c k) : Scheme)
variable [IrreducibleSpace (finiteKernelModel f hL d V c k).left]

/-- The geometric certificates construct an actual point of the entire represented source. -/
theorem finiteModelFppfSource_nonempty_of_etale_certificates
    {Z : Scheme} (a : Z ⟶ A.left) [Etale (a ≫ (v).left)] [Nonempty Z]
    (hg : ∀ x : K, b x = genericPoint T →
      ∃ (B : Scheme) (t : B ⟶ K) (r : B ⟶ D) (z : B), Etale t ∧
        r ≫ p = t ≫ pullback.fst (v).left (v).left ∧
        r ≫ q = t ≫ pullback.snd (v).left (v).left ∧ t z = x) :
    Nonempty (modelFppfSource f hL d V c k v H).left := by
  have hE := finiteModelEffectiveTarget_nonempty_of_generic_etale_lifts f hL d V c k hg
  obtain ⟨y⟩ := modelFppfTarget_nonempty_of_etale_branch f hL d V c k v H a hE
  obtain ⟨x, _⟩ := (modelFppfProjection f hL d V c k v H).left.surjective y
  exact ⟨x⟩

end FLT.Mazur.HilbertChart.AffineRestriction

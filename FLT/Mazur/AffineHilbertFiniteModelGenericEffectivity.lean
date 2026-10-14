/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelGenericPicard
public import FLT.Mazur.KernelPairGenericEffectiveOpen

/-!
# Finite generic inverse data for the original represented Picard region

For an integral selected original source, nonemptiness of the represented
full Picard region is equivalent to a finite collection of actual inverses
covering the entire generic candidate kernel. All finite presentation and
Noetherian hypotheses are supplied by the original finite coefficient model.
Construction of those inverse patches for arbitrary translations remains open.
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
local notation "v" => finiteKernelProjection f hL d V c k
local notation "H" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "m" => pullback.lift p q H
local notation "b" => pullback.fst (Over.Hom.left v) (Over.Hom.left v) ≫ (Over.Hom.left v)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "U" => KernelPairEffectiveOpen.targetOpen p q (Over.Hom.left v) H
variable [IsIntegral A.left]

/-- The represented full Picard region is nonempty exactly when every generic kernel point lifts
on an original scheme open. It is not enough to lift just the diagonal or reduced points. -/
theorem finiteModelPicardFppfTarget_nonempty_iff_genericFiber :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left ↔
      ∀ x : (pullback (v).left (v).left : Scheme),
        b x = genericPoint T → x ∈ MonomorphismOpenImage.locus m := by
  let _ : IsNoetherian A.left := by
    let _ := selectedHilbertSource_isLocallyNoetherian f d V k
    exact ⟨⟩
  rw [finiteModelPicardFppfTarget_nonempty_iff]
  have he : Nonempty (modelEffectiveTarget f hL d V c k v H).left ↔
      (U : Set T).Nonempty := ⟨fun ⟨x⟩ ↦ ⟨x.val, x.property⟩, fun ⟨x, hx⟩ ↦ ⟨⟨x, hx⟩⟩⟩
  rw [he]
  exact KernelPairEffectiveOpen.targetOpen_nonempty_iff_genericFiber p q (v).left H

/-- A finite family of original inverse patches is precisely the remaining generic input. -/
theorem finiteModelPicardFppfTarget_nonempty_iff_finite_patches :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left ↔
      ∃ s : Finset (MonomorphismOpenImage.Patches m),
        ∀ x : (pullback (v).left (v).left : Scheme),
          b x = genericPoint T → ∃ W ∈ s, x ∈ W.val := by
  let _ : IsNoetherian A.left := by
    let _ := selectedHilbertSource_isLocallyNoetherian f d V k
    exact ⟨⟩
  rw [finiteModelPicardFppfTarget_nonempty_iff]
  have he : Nonempty (modelEffectiveTarget f hL d V c k v H).left ↔
      (U : Set T).Nonempty := ⟨fun ⟨x⟩ ↦ ⟨x.val, x.property⟩, fun ⟨x, hx⟩ ↦ ⟨⟨x, hx⟩⟩⟩
  rw [he]
  exact KernelPairEffectiveOpen.targetOpen_nonempty_iff_finite_patches p q (v).left H

/-- Finite generic inverse patches produce an actual original source over the represented region. -/
theorem finiteModelPicardFppfSource_nonempty_of_finite_patches
    (s : Finset (MonomorphismOpenImage.Patches m))
    (hs : ∀ x : (pullback (v).left (v).left : Scheme),
      b x = genericPoint T → ∃ W ∈ s, x ∈ W.val) :
    Nonempty (modelFppfSource f hL d V c k v H).left := by
  rw [finiteModelPicardFppfSource_nonempty_iff,
    ← finiteModelPicardFppfTarget_nonempty_iff]
  exact (finiteModelPicardFppfTarget_nonempty_iff_finite_patches f hL d V c k).mpr ⟨s, hs⟩

end FLT.Mazur.HilbertChart.AffineRestriction

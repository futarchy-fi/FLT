/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelFppfRepresentation
public import FLT.Mazur.SchemeFlatFppfTargetDensity

/-!
# Nonreduced full Picard models with actual flat projections

For a dominant flat model, the represented original Picard fppf image is dense
in its full effective target. Nonemptiness passes to the represented image
without integrality or reduction of the original coefficient schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  {T : Over (Spec (.of R))} (w : A ⟶ T)
  (hw : (fst f hL d V c k).left ≫ w.left = (snd f hL d V c k).left ≫ w.left)
  [LocallyOfFinitePresentation w.left] [Flat w.left] [IsDominant w.left]
local notation "g" => modelEffectiveRelativeProjection f hL d V c k w hw
local notation "E" => modelEffectiveTarget f hL d V c k w hw
local notation "U" => KernelPairEffectiveOpen.targetOpen
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k)) w.left hw

/-- The original represented region is dense, retaining all nonreduced model structure. -/
theorem modelFppfLocus_dense_of_flat :
    Dense (SchemeFppfTargetOpen.locus (g).left : Set (E).left) :=
  SchemeFppfTargetOpen.dense_open_baseChange_of_flat w.left (U).ι

/-- Flat model geometry replaces the integral-source generic-flatness hypothesis. -/
theorem modelFppfTarget_nonempty_iff_of_flat :
    Nonempty (modelFppfTarget f hL d V c k w hw).left ↔ Nonempty (E).left := by
  refine ⟨fun ⟨y⟩ ↦ ⟨(modelFppfToEffectiveTarget f hL d V c k w hw).left y⟩, ?_⟩
  intro hE
  obtain ⟨y, hy⟩ :=
    (SchemeFppfTargetOpen.nonempty_open_baseChange_iff_of_flat w.left (U).ι).mpr hE
  exact ⟨⟨y, hy⟩⟩

/-- Every effective neighborhood contains points of the actual represented Picard image. -/
theorem modelFppfLocus_inter_nonempty_of_flat (W : (E).left.Opens)
    (hW : (W : Set (E).left).Nonempty) :
    ((W : Set (E).left) ∩ SchemeFppfTargetOpen.locus (g).left).Nonempty :=
  (modelFppfLocus_dense_of_flat f hL d V c k w hw).inter_open_nonempty W W.isOpen hW

/-- The complete original source over this represented region is also nonempty. -/
theorem modelFppfSource_nonempty_iff_of_flat :
    Nonempty (modelFppfSource f hL d V c k w hw).left ↔ Nonempty (E).left := by
  rw [← modelFppfTarget_nonempty_iff_of_flat f hL d V c k w hw]
  constructor
  · rintro ⟨x⟩
    exact ⟨(modelFppfProjection f hL d V c k w hw).left x⟩
  · rintro ⟨y⟩
    obtain ⟨x, _⟩ := (modelFppfProjection f hL d V c k w hw).left.surjective y
    exact ⟨x⟩

end FLT.Mazur.HilbertChart.AffineRestriction

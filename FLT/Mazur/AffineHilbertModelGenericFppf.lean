/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelFppfRepresentation
public import FLT.Mazur.SchemeGenericFppfTargetOpen

/-!
# Generic fppf density inside full effective Picard models

For a dominant quasi-compact model over an integral target, passage from the
full effective region to the represented fppf region preserves nonemptiness.
Flatness and surjectivity need not be hypotheses. The remaining nonemptiness
question is precisely that of the full effective region, not generic flatness.
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
  [LocallyOfFinitePresentation w.left] [QuasiCompact w.left] [IsDominant w.left]
  [IsIntegral T.left]
local notation "g" => modelEffectiveRelativeProjection f hL d V c k w hw
local notation "E" => modelEffectiveTarget f hL d V c k w hw
local notation "U" => KernelPairEffectiveOpen.targetOpen
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k)) w.left hw

/-- The actual represented fppf open is dense inside the original full effective region. -/
theorem modelFppfLocus_dense :
    Dense (SchemeFppfTargetOpen.locus (g).left : Set (E).left) :=
  SchemeFppfTargetOpen.dense_open_baseChange w.left (U).ι

/-- The comparison into the effective model is dominant without assuming global flatness. -/
instance modelFppfToEffectiveTarget_isDominant :
    IsDominant (modelFppfToEffectiveTarget f hL d V c k w hw).left := by
  constructor
  change Dense (Set.range (SchemeFppfTargetOpen.locus (g).left).ι)
  rw [Scheme.Opens.range_ι]
  exact modelFppfLocus_dense f hL d V c k w hw

/-- Effective nonemptiness is equivalent to nonemptiness of the represented fppf target. -/
theorem modelFppfTarget_nonempty_iff :
    Nonempty (modelFppfTarget f hL d V c k w hw).left ↔ Nonempty (E).left := by
  refine ⟨fun ⟨y⟩ ↦ ⟨(modelFppfToEffectiveTarget f hL d V c k w hw).left y⟩, ?_⟩
  intro hE
  obtain ⟨y, hy⟩ := (SchemeFppfTargetOpen.nonempty_open_baseChange_iff w.left (U).ι).mpr hE
  exact ⟨⟨y, hy⟩⟩

/-- Every nonempty effective open meets the represented region. -/
theorem modelFppfLocus_inter_nonempty (W : (E).left.Opens)
    (hW : (W : Set (E).left).Nonempty) :
    ((W : Set (E).left) ∩ SchemeFppfTargetOpen.locus (g).left).Nonempty :=
  (modelFppfLocus_dense f hL d V c k w hw).inter_open_nonempty W W.isOpen hW

/-- The complete retained original source is nonempty exactly when the effective target is. -/
theorem modelFppfSource_nonempty_iff :
    Nonempty (modelFppfSource f hL d V c k w hw).left ↔ Nonempty (E).left := by
  rw [← modelFppfTarget_nonempty_iff f hL d V c k w hw]
  constructor
  · rintro ⟨x⟩
    exact ⟨(modelFppfProjection f hL d V c k w hw).left x⟩
  · rintro ⟨y⟩
    obtain ⟨x, _⟩ := (modelFppfProjection f hL d V c k w hw).left.surjective y
    exact ⟨x⟩

end FLT.Mazur.HilbertChart.AffineRestriction

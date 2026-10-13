/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertComposableEnvelope
public import FLT.Mazur.AffineHilbertRelationOperations
public import FLT.Mazur.SchemeOpenEnvelopeLocus

/-!
# Invariance of the constructed full-envelope locus

Composition transports a full independent translation fiber across every
original relation arrow. Thus the complement of the missing-envelope image
is invariant, without assuming that the projection is closed or that any
nonvanishing invariant coefficient has already been found.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => toEnvelope f hL d V c k
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "e" => equivalence f hL d V c k

/-- Composition retains the independent first translation and the second arrow's test point. -/
theorem composable_fullEnvelope_transport :
    (e).t ≫ j = composableToProduct f hL d V c k ≫ prod.map q (𝟙 V) := by
  apply prod.hom_ext
  · simp only [Category.assoc, toEnvelope_test, prod.map_fst,
      composableToProduct, prod.lift_fst_assoc]
    exact (e).transitivity₂
  · simp only [Category.assoc, prod.map_snd, Category.comp_id,
      composableToProduct, prod.lift_snd, toEnvelope_base]
    rw [← Category.assoc, ← Category.assoc, (e).transitivity₁]
    rfl

variable [IsOpenImmersion k.left]

/-- The actual source set on which every independent translation belongs to the full relation. -/
def fullEnvelopeLocus : Set A.left := fullFiberLocus π (j).left.opensRange

/-- A full fiber at the first endpoint gives a full fiber at the second endpoint. -/
theorem fullEnvelopeLocus_snd_of_fst (z : (Z).left)
    (hz : (p).left z ∈ fullEnvelopeLocus f hL d V c k) :
    (q).left z ∈ fullEnvelopeLocus f hL d V c k := by
  apply (mem_fullFiberLocus π (j).left.opensRange _).mpr
  intro y hy
  obtain ⟨w, hw, hwz⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_prod_fst_with_id q V).map (Over.forget _)).flip y z hy
  change (prod.map q (𝟙 V)).left w = y at hw
  change (prod.fst : prod Z V ⟶ Z).left w = z at hwz
  have hpw : π ((prod.map p (𝟙 V)).left w) = (p).left z := by
    change ((prod.map p (𝟙 V)).left ≫ π) w = _
    rw [← Over.comp_left, prod.map_fst]
    change (p).left ((prod.fst : prod Z V ⟶ Z).left w) = _
    rw [hwz]
  obtain ⟨r, hr⟩ := (mem_fullFiberLocus π (j).left.opensRange _).mp hz
    ((prod.map p (𝟙 V)).left w) hpw
  obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback
    ((composableToProduct_isPullback f hL d V c k).map (Over.forget _)) r w hr
  change (composableToProduct f hL d V c k).left a = w at ha
  refine ⟨(e).t.left a, ?_⟩
  change ((e).t ≫ j).left a = y
  rw [composable_fullEnvelope_transport]
  change (prod.map q (𝟙 V)).left ((composableToProduct f hL d V c k).left a) = y
  rw [ha, hw]

/-- The constructed full-envelope locus is invariant for the ORIGINAL complete relation. -/
theorem fullEnvelopeLocus_invariant :
    (p).left ⁻¹' fullEnvelopeLocus f hL d V c k =
      (q).left ⁻¹' fullEnvelopeLocus f hL d V c k := by
  ext z
  constructor
  · exact fullEnvelopeLocus_snd_of_fst f hL d V c k z
  · intro hz
    have hs₁ : (p).left ((e).s.left z) = (q).left z :=
      congrArg (fun g ↦ g.left z) (e).symmetry₁
    have hs₂ : (q).left ((e).s.left z) = (p).left z :=
      congrArg (fun g ↦ g.left z) (e).symmetry₂
    have h := fullEnvelopeLocus_snd_of_fst f hL d V c k ((e).s.left z) (hs₁ ▸ hz)
    rwa [hs₂] at h

end FLT.Mazur.HilbertChart.AffineRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertAdmissibleGenericPoint

/-!
# A nonzero admissible original coefficient constructs a represented Picard region

For an integral original source, its generic point maps to the generic point
of the OLD finite model by the proved dominance of its coefficient inclusion.
Any nonempty admissible principal open contains that source generic point.
Thus one original admissible point anywhere constructs generic coverage and
a nonempty represented Picard fppf region; it need not start over the generic fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsIntegral A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => finiteKernelProjection f hL d V c k
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "C" => compatibleFunctions
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k))

/-- The actual original generic parameter lies over the old model's generic coefficient point. -/
theorem finiteKernelProjection_genericPoint :
    (v).left (genericPoint A.left) = genericPoint T := by
  apply IsGenericPoint.eq _ (genericPoint_spec T)
  have hg := (genericPoint_spec A.left).image (v).left.continuous
  simpa only [Set.image_univ, (v).left.denseRange.closure_range] using hg

/-- Nonemptiness somewhere in the original source constructs coverage of every generic branch. -/
theorem integral_generic_admissible_coverage (s : C)
    (hs : s ∈ invariantEnvelopeDenominators f hL d V c k)
    (hne : (A.left.basicOpen s.val : Set A.left).Nonempty) :
    ∀ y : A.left, (v).left y = genericPoint T →
      ∃ t : C, t ∈ invariantEnvelopeDenominators f hL d V c k ∧
        y ∈ A.left.basicOpen t.val := by
  obtain ⟨x, hx⟩ := hne
  have hg : genericPoint A.left ∈ A.left.basicOpen s.val :=
    (genericPoint_specializes x).mem_open (A.left.basicOpen s.val).isOpen hx
  exact generic_admissible_source_coverage f hL d V c k (genericPoint A.left)
    (finiteKernelProjection_genericPoint f hL d V c k) s hs hg

variable [IsAffine V.left]

/-- A nonempty admissible original principal gives a nonempty represented original Picard region. -/
theorem finiteModelPicardFppfTarget_nonempty_of_admissible_source (s : C)
    (hs : s ∈ invariantEnvelopeDenominators f hL d V c k)
    (hne : (A.left.basicOpen s.val : Set A.left).Nonempty) :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left :=
  finiteModelPicardFppfTarget_nonempty_of_admissible_coverage f hL d V c k
    (integral_generic_admissible_coverage f hL d V c k s hs hne)

/-- On the integral original source, a nonzero coefficient suffices; no point is chosen as input. -/
theorem finiteModelPicardFppfTarget_nonempty_of_nonzero_admissible (s : C)
    (hs : s ∈ invariantEnvelopeDenominators f hL d V c k) (hne : s ≠ 0) :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left := by
  apply finiteModelPicardFppfTarget_nonempty_of_admissible_source f hL d V c k s hs
  apply (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp
  intro he
  apply hne
  apply Subtype.ext
  exact (basicOpen_eq_bot_iff s.val).mp he

/-- A single nonzero element of the actual denominator ideal constructs represented nonemptiness. -/
theorem finiteModelPicardFppfTarget_nonempty_of_denominators_ne_bot
    (hI : invariantEnvelopeDenominators f hL d V c k ≠ ⊥) :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left := by
  obtain ⟨s, hs, hne⟩ := (Submodule.ne_bot_iff _).mp hI
  exact finiteModelPicardFppfTarget_nonempty_of_nonzero_admissible f hL d V c k s hs hne

end FLT.Mazur.HilbertChart.AffineRestriction

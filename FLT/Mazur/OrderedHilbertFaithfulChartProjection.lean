/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulChartComparison
public import FLT.Mazur.AcyclicHilbertFixedBaseRetraction
public import FLT.Mazur.VariableHilbertFixedBaseProjection

/-!
# The localized faithful chart projects to the actual original chart

The complete scheme morphism, not just its Picard class, recovers the original
parameter on every faithful affine test. Both independent coordinates are
compared through the constructed original-test isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertFaithfulTestCover
open HilbertChart CartierAbel SchemePicard FCurve AffineEtaleFaithfulNeighborhood
open OrderedHilbertAffineEtaleTestCover
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "b" => fun x ↦ spectrumBase
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))
local notation "q" => fun x ↦ FaithfulNeighborhoodCurve.map f
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))
local notation "degree" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))

/-- The localized chart parameter projects to the actual ORIGINAL chart map. -/
theorem localChartParameter_projection (x : T.left) :
    (Over.map (b x)).map (localChartParameter f hL T s x) ≫
        variableHilbertFixedBaseProjection f (b x) hL (degree x) (E x)
          (localTranslation f hL T s x) (translationToOriginal f hL T s x) =
      (originalTestIso f hL T s x).hom ≫ toOriginalChart f hL T s x := by
  apply prod.hom_ext
  · change _ ≫ variableHilbertBase f (degree x) (E x) =
      _ ≫ variableHilbertBase f (degree x) (E x)
    rw [Category.assoc, variableHilbertFixedBaseProjection_base,
      ← Functor.map_comp_assoc, localChartParameter_base]
    simpa only [toOriginalChart, coordinate, faithfulOverlapCoordinate, Category.assoc] using
      coordinate_base_comparison f hL T s x
  · change _ ≫ variableHilbertParameter f (degree x) (E x) =
      _ ≫ variableHilbertParameter f (degree x) (E x)
    rw [Category.assoc, variableHilbertFixedBaseProjection_hilbert,
      ← Functor.map_comp_assoc, localChartParameter_hilbert, localHilbertParameter,
      acyclicHilbertFixedBaseParameter_projection]
    rfl

end FLT.Mazur.OrderedHilbertFaithfulTestCover

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulPicardComparison
public import FLT.Mazur.AcyclicHilbertFixedBaseIdeal

/-!
# Original Hilbert parameters over constructed faithful coefficient neighborhoods

Each member of the original varying-chart affine cover gives an actual
Hilbert parameter for the localized proper curve. Its full ideal is precisely
the original full ideal pulled along the already constructed test-curve iso.
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

/-- The retained original acyclic Hilbert parameter of the affine test. -/
def originalHilbertParameter (x : T.left) :
    test f hL T s x ⟶ acyclicHilbertTest f (degree x) :=
  toOriginalChart f hL T s x ≫ variableHilbertParameter f (degree x) (E x)

/-- An actual parameter on the Hilbert scheme constructed from the localized proper curve. -/
def localHilbertParameter (x : T.left) :
    localTest f hL T s x ⟶ acyclicHilbertTest (q x) (degree x) :=
  acyclicHilbertFixedBaseParameter f (b x) hL (degree x) (localTest f hL T s x)
    ((originalTestIso f hL T s x).hom ≫ originalHilbertParameter f hL T s x)

/-- The local Hilbert parameter retains the entire original universal ideal on the test. -/
theorem localHilbertParameter_ideal (x : T.left) :
    (acyclicHilbertParameterDivisor (q x) (degree x) (localTest f hL T s x)
      (localHilbertParameter f hL T s x)).val.val =
        (acyclicHilbertParameterDivisor f (degree x) (test f hL T s x)
          (originalHilbertParameter f hL T s x)).val.val.comap
            (testCurveIso f hL T s x).hom := by
  rw [localHilbertParameter, acyclicHilbertFixedBaseParameter_ideal,
    acyclicHilbertParameterDivisor_eq, acyclicHilbertParameterDivisor_eq,
    finiteTypeAcyclicDivisorMap_ideal, finiteTypeAcyclicDivisorMap_ideal,
    relativeTotalMap_comp]
  simp only [testCurveIso, Iso.trans_hom, ← Scheme.IdealSheafData.comap_comp,
    Category.assoc]

end FLT.Mazur.OrderedHilbertFaithfulTestCover

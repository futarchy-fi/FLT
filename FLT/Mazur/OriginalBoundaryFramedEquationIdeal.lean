/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFramedEquations
public import FLT.Mazur.OriginalBoundaryFiniteComparisonTests
public import FLT.Mazur.RelativeExactRankFinite

/-!
# Exact images and ideals of the original framed comparison

The coordinate equations cover the actual original comparison scheme. Their
images compute its full image, and their exact ideals compute its exact kernel.
The original rank supplies full-source finiteness before the kernel calculation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem framedCover_range {X Y : Scheme.{0}} (g : X ⟶ Y) (C : X.OpenCover)
    (j : ∀ i : C.I₀, C.X i ⟶ Y) (hj : ∀ i, C.f i ≫ g = j i) :
    Set.range g = ⋃ i : C.I₀, Set.range (j i) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨i, v, rfl⟩ := C.exists_eq w
    exact Set.mem_iUnion.mpr ⟨i, v, (congrArg (fun k ↦ k v) (hj i)).symm⟩
  · intro hz
    obtain ⟨i, v, rfl⟩ := Set.mem_iUnion.mp hz
    exact ⟨C.f i v, congrArg (fun k ↦ k v) (hj i)⟩

private theorem framedCover_kernel {X Y : Scheme.{0}} (g : X ⟶ Y) [QuasiCompact g]
    (C : X.OpenCover) (j : ∀ i : C.I₀, C.X i ⟶ Y) (hj : ∀ i, C.f i ≫ g = j i) :
    g.ker = ⨅ i : C.I₀, (j i).ker :=
  (g.iInf_ker_openCover_map_comp C).symm.trans
    (iInf_congr fun i ↦ congrArg Scheme.Hom.ker (hj i))

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "P" => pullback.snd p J.subschemeι
local notation "Q" => InvariantIdealRelation.snd J p q hJ
local notation "E" => Over.mk P
local notation "c" => originalBoundaryComparison p q J hJ
local instance equationIdealBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance equationIdealBoundaryOver_etale : Etale (E).hom := inferInstanceAs (Etale P)
local instance equationIdealBoundaryOver_compact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact P)
local instance equationIdealOriginalOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance equationIdealOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance equationIdealOriginalOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (t : B ⟶ pullback
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (n : ℕ)
local notation "x" => t ≫ pullback.fst f f
local notation "y" => t ≫ pullback.snd f f
variable (a : Over.mk (t ≫ pullback.fst _ _) ⟶
    distinctScheme (Over.mk (pullback.snd p J.subschemeι)) (Fin n))
  (ht : Set.range (t ≫ pullback.fst _ _ ≫ J.subschemeι) ⊆ exactRank (Over.mk p) n)

attribute [local irreducible] scalarMorphism
include ht

/-- The full coordinate equations are an actual open cover of the original comparison. -/
def originalBoundaryFrameEquationCover : (pullback c t).OpenCover where
  I₀ := Fin n
  X := frameEquationChart E (Fin n) a Q y
  «f» := originalBoundaryFrameEquationMap J hJ t n a
  mem₀ := ((frameEquationCover E (Fin n) a Q y
    (originalBoundary_frame_complete J t n a ht)).pushforwardIso
      (RelationComparisonEquation.iso P Q f c (pullback.lift_fst _ _ _)
        (pullback.lift_snd _ _ _) t).inv).mem₀

/-- Cover maps are the previously constructed actual original arrows. -/
theorem originalBoundaryFrameEquationCover_map (i : Fin n) :
    (originalBoundaryFrameEquationCover J hJ t n a ht).f i =
      originalBoundaryFrameEquationMap J hJ t n a i := rfl

attribute [local irreducible] originalBoundaryFrameEquationMap

/-- Actual comparison coverage is exactly the union of full coordinate equation images. -/
theorem originalBoundary_frameEquation_range :
    Set.range (pullback.snd c t) = ⋃ i : Fin n, Set.range
      (equalizer.ι
        (testSection E (Fin n) a i ≫ pullback.fst P x ≫ Q)
        (testSection E (Fin n) a i ≫ pullback.snd P x ≫ y)) :=
  framedCover_range (pullback.snd c t) (originalBoundaryFrameEquationCover J hJ t n a ht)
    _ (fun i ↦ originalBoundaryFrameEquationMap_snd J hJ t n a i)

variable [IsAffine A] [LocallyQuasiFinite p]
local instance equationIdealOriginal_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›

/-- The original rank constructs finiteness of the whole comparison before taking its ideal. -/
theorem originalBoundary_exactRank_comparison_finite : IsFinite (pullback.snd c t) := by
  let _ : IsFinite (pullback.snd p (t ≫ pullback.fst f f ≫ J.subschemeι)) :=
    finite_pullback_of_exactRank (Over.mk p) n _ ht
  exact originalBoundary_comparison_test_finite J hJ t

/-- The exact original comparison ideal is the intersection of all full coordinate equations. -/
theorem originalBoundary_frameEquation_kernel :
    (pullback.snd c t).ker = ⨅ i : Fin n,
      (equalizer.ι
        (testSection E (Fin n) a i ≫ pullback.fst P x ≫ Q)
        (testSection E (Fin n) a i ≫ pullback.snd P x ≫ y)).ker := by
  let _ := originalBoundary_exactRank_comparison_finite J hJ t n ht
  exact framedCover_kernel (pullback.snd c t)
    (originalBoundaryFrameEquationCover J hJ t n a ht) _
    (fun i ↦ originalBoundaryFrameEquationMap_snd J hJ t n a i)

end FLT.Mazur.EquivalenceRelationOrderedFrames

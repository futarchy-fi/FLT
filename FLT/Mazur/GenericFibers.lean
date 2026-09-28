/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.Contracts
public import FLT.Mazur.CurveFinite
public import FLT.Mazur.RationalFibers
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.HomCongr

/-!
# Finite rational fibers of the generic quotient

Points over the given generic map are sections of its scheme-theoretic pullback.
Distinct cusp images imply a nonconstant generic morphism. For a proper integral
generic curve of dimension at most one and a separated target, FC14 and FC15
give finite rational fibers. Finiteness of the target points then gives
finiteness of the source points.

All geometric and arithmetic inputs remain explicit. In particular the
dimension bound and finiteness of the quotient points are not constructed here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace FLT.Mazur
namespace Points

/-- Points over a field-valued base map are sections of the pullback to that field. -/
def pullbackEquiv {S : Scheme.{u}} (X : Over S) {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) :
    Points X s ≃ Sections ((Over.pullback s).obj X) :=
  ((Over.isoMk (Iso.refl _) (by simp) :
      Over.mk s ≅ (Over.map s).obj (Over.mk (𝟙 (Spec (CommRingCat.of K))))).homCongr
        (Iso.refl X)).trans
    ((Over.mapPullbackAdj s).homEquiv (Over.mk (𝟙 (Spec (CommRingCat.of K)))) X)

/-- The point/section comparison commutes with projection to another scheme. -/
theorem pullbackEquiv_map {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (a : Points X s) :
    pullbackEquiv Y s (map f a) =
      Sections.map ((Over.pullback s).map f) (pullbackEquiv X s a) := by
  simp only [pullbackEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, map, Sections.map]
  rw [← Category.assoc, (Over.mapPullbackAdj s).homEquiv_naturality_right]

/-- A finite generic scheme morphism has finite fibers on the original point sets. -/
theorem finite_fiber {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    [IsFinite ((Over.pullback s).map f).left] (a : Points Y s) :
    Finite {x : Points X s // map f x = a} := by
  let : Finite (Sections.Fiber ((Over.pullback s).map f) (pullbackEquiv Y s a)) :=
    Sections.finite_fiber _ _
  let lift : {x : Points X s // map f x = a} →
      Sections.Fiber ((Over.pullback s).map f) (pullbackEquiv Y s a) :=
    fun x ↦ ⟨pullbackEquiv X s x.val, by rw [← pullbackEquiv_map, x.property]⟩
  apply Finite.of_injective lift
  intro x y h
  exact Subtype.ext ((pullbackEquiv X s).injective (congrArg Subtype.val h))

end Points

/-- The documented proper smooth geometrically integral curve input. -/
def G1Geometry {p : ℕ} (D : IntegralData p) : Prop :=
  IsProper D.X.hom ∧ SmoothOfRelativeDimension 1 D.X.hom ∧ GeometricallyIntegral D.X.hom

/-- Finiteness of the supplied quotient's rational generic points. -/
def G2Finite {p : ℕ} {D : IntegralData p} (Q : QuotientData D) : Prop :=
  Finite (Points Q.A D.generic)

/-- The exact finite-fiber consequence required by the two-cusp argument. -/
def G2Fibers {p : ℕ} {D : IntegralData p} (Q : QuotientData D) : Prop :=
  ∀ a : Points Q.A D.generic, Finite {x : Points D.X D.generic // onGeneric Q x = a}

/-- Finiteness of the supplied curve's rational generic points. -/
def G2CurveFinite {p : ℕ} (D : IntegralData p) : Prop :=
  Finite (Points D.X D.generic)

/-- The scheme-theoretic generic fiber of the supplied integral curve. -/
abbrev IntegralData.genericFiber {p : ℕ} (D : IntegralData p) :
    Over (Spec (CommRingCat.of ℚ)) :=
  (Over.pullback D.generic).obj D.X

/-- The documented integral geometry supplies properness and integrality of the generic curve. -/
theorem IntegralData.generic_geometry {p : ℕ} (D : IntegralData p)
    (hgeometry : G1Geometry D) :
    IsProper D.genericFiber.hom ∧ IsIntegral D.genericFiber.left := by
  obtain ⟨hp, _, hi⟩ := hgeometry
  let : IsProper D.X.hom := hp
  let : GeometricallyIntegral D.X.hom := hi
  have hproper : IsProper D.genericFiber.hom := by
    change IsProper (pullback.snd D.X.hom D.generic)
    infer_instance
  have hintegral : GeometricallyIntegral D.genericFiber.hom := by
    change GeometricallyIntegral (pullback.snd D.X.hom D.generic)
    infer_instance
  exact ⟨hproper, GeometricallyIntegral.isIntegral_of_subsingleton D.genericFiber.hom⟩

namespace QuotientData

variable {p : ℕ} {D : IntegralData p} (Q : QuotientData D)

/-- The quotient target after base change along the given generic map. -/
abbrev genericFiber : Over (Spec (CommRingCat.of ℚ)) :=
  (Over.pullback D.generic).obj Q.A

/-- The canonical generic projection, obtained by functorial base change. -/
abbrev genericProjection : D.genericFiber ⟶ Q.genericFiber :=
  (Over.pullback D.generic).map Q.projection

/-- Distinct projected cusps imply geometric nonconstancy of the generic projection. -/
theorem genericProjection_nonconstant (hc : G2Cusps Q) :
    ∃ a b : D.genericFiber.left, Q.genericProjection.left a ≠ Q.genericProjection.left b := by
  apply FCurve.distinctSectionImages Q.genericProjection
    (Points.pullbackEquiv D.X D.generic (genericSection D D.cuspZero))
    (Points.pullbackEquiv D.X D.generic (genericSection D D.cuspInfinity))
  intro h
  apply hc
  apply (Points.pullbackEquiv Q.A D.generic).injective
  simpa only [onGeneric, Points.pullbackEquiv_map, Sections.map, genericProjection] using h

/-- The generic projection is finite once the curve geometry and cusp separation are supplied. -/
theorem isFinite_genericProjection (hc : G2Cusps Q)
    [IsProper D.genericFiber.hom] [IsIntegral D.genericFiber.left]
    [IsSeparated Q.genericFiber.hom]
    (hdim : topologicalKrullDim D.genericFiber.left ≤ 1) :
    IsFinite Q.genericProjection.left :=
  FCurve.nonconstantProperCurveFinite D.genericFiber.hom Q.genericFiber.hom
    Q.genericProjection.left inferInstance inferInstance hdim inferInstance
    (Over.w Q.genericProjection) (Q.genericProjection_nonconstant hc)

/-- The geometric curve argument supplies the finite rational-fiber contract. -/
theorem g2Fibers (hc : G2Cusps Q)
    [IsProper D.genericFiber.hom] [IsIntegral D.genericFiber.left]
    [IsSeparated Q.genericFiber.hom]
    (hdim : topologicalKrullDim D.genericFiber.left ≤ 1) : G2Fibers Q := by
  let := Q.isFinite_genericProjection hc hdim
  intro a
  exact Points.finite_fiber Q.projection D.generic a

/-- Finite fibers over finitely many quotient points give finitely many curve points. -/
theorem g2CurveFinite_of_fibers (hf : G2Fibers Q) (hfinite : G2Finite Q) :
    G2CurveFinite D := by
  let : Finite (Points Q.A D.generic) := hfinite
  let : ∀ a : Points Q.A D.generic,
      Finite {x : Points D.X D.generic // onGeneric Q x = a} := hf
  exact Finite.of_equiv _ (Equiv.sigmaFiberEquiv (onGeneric Q))

/-- Curve-point finiteness from the documented geometric, cusp and quotient inputs.
The smooth-to-topological-dimension bridge remains an explicit bound here. -/
theorem g2CurveFinite (hgeometry : G1Geometry D)
    (hc : G2Cusps Q) (hfinite : G2Finite Q) [IsSeparated Q.A.hom]
    (hdim : topologicalKrullDim D.genericFiber.left ≤ 1) : G2CurveFinite D := by
  obtain ⟨hp, hi⟩ := D.generic_geometry hgeometry
  let : IsProper D.genericFiber.hom := hp
  let : IsIntegral D.genericFiber.left := hi
  let : IsSeparated Q.genericFiber.hom := by
    change IsSeparated (pullback.snd Q.A.hom D.generic)
    infer_instance
  exact Q.g2CurveFinite_of_fibers (Q.g2Fibers hc hdim) hfinite

end QuotientData
end FLT.Mazur

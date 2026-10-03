/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleDualSectionCancellation
public import FLT.Mazur.ProjectiveLineMarkedPullbackCoordinates
public import FLT.Mazur.ProjectiveLineMarkedTransition
/-!
# Laurent transition of actual marked divisor sections

The two polynomial coordinates of every global section of the marked divisor
power satisfy the Laurent transition, with sign and reciprocal coordinate.
The proof transports rank-one coordinate relations to the overlap and cancels
the canonical Cartier section by its regular dual evaluation.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineMarkedSectionTransition
open FCurve PolygonDivisorNormalizationPullback
open ProjectiveLineMarkedCharts ProjectiveLineMarkedDualCoordinates
open ProjectiveLineMarkedPullbackCoordinates
variable (K : Type u) [Field K]
/-- The actual positive marked divisor power on the projective line. -/
abbrev line (a : Kˣ) (m : ℕ) :=
  divisorLineBundle ((markedPoint K a).ker ^ m) ((relativeCartier K a).1.pow m)
/-- Polynomial coordinate of an actual global section on a marked chart. -/
def polynomial (a : Kˣ) (m : ℕ)
    (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K) [IsOpenImmersion j]
    (b : K) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) : K[X] :=
  (coordinateRing K).symm (chartSectionsCoordinate K a j b hj m
    (((pullback j).map s).app ⊤
      ((modulePullbackUnitIso j).inv.app ⊤ (1 : Γ(ProjectiveLine.chart K, ⊤)))))
/-- The polynomial on the chart with the original marked coordinate. -/
def leftPolynomial (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) : K[X] :=
  polynomial K a m (ProjectiveLine.left K) a (left_ideal K a) s
/-- The polynomial on the reciprocal chart. -/
def rightPolynomial (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) : K[X] :=
  polynomial K a m (ProjectiveLine.right K) (a⁻¹ : Kˣ) (right_ideal K a) s

/-- The canonical Laurent coordinate ring of the overlap. -/
def laurentRing : K[T;T⁻¹] ≃+* Γ(ProjectiveLine.overlap K, ⊤) :=
  (Scheme.ΓSpecIso (.of K[T;T⁻¹])).symm.commRingCatIsoToRingEquiv
/-- The left overlap map induces the polynomial inclusion into Laurent polynomials. -/
lemma left_coordinate (p : K[X]) :
    (ProjectiveLine.overlapLeft K).appTop (coordinateRing K p) =
      laurentRing K (Polynomial.toLaurent p) := by
  exact (congrArg (fun k ↦ k.hom p) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.toLaurent : K[X] →+* K[T;T⁻¹])))).symm
/-- The right overlap map induces Laurent inversion after polynomial inclusion. -/
lemma right_coordinate (p : K[X]) :
    (ProjectiveLine.overlapRight K).appTop (coordinateRing K p) =
      laurentRing K (LaurentPolynomial.invert (Polynomial.toLaurent p)) := by
  have hi : ProjectiveLine.overlapRight K = Spec.map (CommRingCat.ofHom
      ((LaurentPolynomial.invert (R := K)).toRingHom.comp Polynomial.toLaurent)) := by
    simp only [ProjectiveLine.overlapRight, ProjectiveLine.inversion_hom,
      ProjectiveLine.overlapLeft, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [hi]
  exact (congrArg (fun k ↦ k.hom p) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom
      ((LaurentPolynomial.invert (R := K)).toRingHom.comp Polynomial.toLaurent)))).symm
/-- The canonical section has its powered equation as chart coordinate. -/
lemma coordinate_canonical (a : Kˣ) (m : ℕ)
    (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K) [IsOpenImmersion j]
    (b : K) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker) :
    chartSectionsCoordinate K a j b hj m
      (pullGlobal j (line K a m) (divisorSection ((relativeCartier K a).1.pow m) ⊤)) =
      equation K b ^ m := by
  rw [divisorSection, pullGlobal_hom, chartSectionsCoordinate_canonical]
/-- The canonical section cancels scalars on the Laurent overlap. -/
lemma canonical_cancel (a : Kˣ) (m : ℕ) :
    Function.Injective (fun r : Γ(ProjectiveLine.overlap K, ⊤) ↦
      r • pullGlobal (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K)
        (line K a m) (divisorSection ((relativeCartier K a).1.pow m) ⊤)) := by
  intro r t h
  apply pullGlobal_divisor_smul_cancel (ProjectiveLine.overlapLeft K)
    ((effectiveCartier K (a : K)).pow m)
    (show CartierChart ((chartPoint K (a : K)).ker ^ m) (chartTop K) from
      ⟨equation K (a : K) ^ m, (equation_regular K (a : K)).pow m,
        power_equation K (a : K) m⟩)
  have h' := congrArg (fun z ↦
    ((pullback (ProjectiveLine.overlapLeft K)).map (leftPowerIso K a m).hom).app ⊤
      (((pullbackComp (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K)).inv.app
        (line K a m)).app ⊤ z)) h
  simp only [Hom.app_smul, pullGlobal_comp, pullGlobal_naturality] at h'
  have he : (leftPowerIso K a m).hom.app ⊤
      (pullGlobal (ProjectiveLine.left K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤)) =
      divisorSection ((effectiveCartier K (a : K)).pow m) ⊤ := by
    rw [divisorSection, pullGlobal_hom]
    exact divisorLinePullbackIsoOfEq_section_apply _ _ _ _ ⊤
  rw [he] at h'
  exact h'
/-- The polynomial coordinate agrees with the semilinear section pullback. -/
lemma polynomial_coordinate (a : Kˣ) (m : ℕ)
    (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K) [IsOpenImmersion j]
    (b : K) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    coordinateRing K (polynomial K a m j b hj s) =
      chartSectionsCoordinate K a j b hj m
        (pullGlobal j (line K a m) (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤)))) := by
  rw [polynomial, RingEquiv.apply_symm_apply, pullGlobal_hom]

/-- The two canonical-section coordinates have the specified Laurent transition. -/
lemma canonical_transition (a : Kˣ) (m : ℕ) :
    (ProjectiveLine.overlapRight K).appTop (equation K (a⁻¹ : Kˣ) ^ m) =
      laurentRing K ((ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m) *
        (ProjectiveLine.overlapLeft K).appTop (equation K (a : K) ^ m) := by
  simp only [equation, ← map_pow, left_coordinate, right_coordinate]
  rw [ProjectiveLineMarkedTransition.power_transition, map_mul]

/-- Every actual global section satisfies the marked Laurent transition. -/
theorem transition (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    LaurentPolynomial.invert (Polynomial.toLaurent (rightPolynomial K a m s)) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m *
        Polynomial.toLaurent (leftPolynomial K a m s) := by
  apply (laurentRing K).injective
  rw [map_mul, ← left_coordinate, ← right_coordinate]
  unfold leftPolynomial rightPolynomial
  rw [polynomial_coordinate, polynomial_coordinate]
  apply pullGlobal_coordinate_transition
    (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K)
    (ProjectiveLine.overlapRight K) (ProjectiveLine.right K)
    (ProjectiveLine.overlap_condition K) (line K a m)
    (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m)
    (chartSectionsCoordinate K a (ProjectiveLine.right K) (a⁻¹ : Kˣ) (right_ideal K a) m)
    (divisorSection ((relativeCartier K a).1.pow m) ⊤)
    (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤)))
    (laurentRing K ((ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m))
    (canonical_cancel K a m)
  rw [coordinate_canonical, coordinate_canonical]
  exact canonical_transition K a m
end FLT.Mazur.ProjectiveLineMarkedSectionTransition

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalZeroRetainedChart
import all FLT.Mazur.WeierstrassNodalZeroRetainedChart
public import FLT.Mazur.WeierstrassModificationXFiberConicOpen

/-!
# The complete first retained conic and incidence line at depth zero

Both pieces occupy the actual integral tangent model and cover exactly its
first retained chart. The full conic incidence open remains cartesian after
the genuine tangent specialization, including its scheme structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {depth n : ℕ}
  (hbound : 2 * (0 + n) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (j : ℕ) (hj : j ≤ n) (hpos : 0 < j)
include hpos
local notation "data" => nodalDepthFamily hm hbound h3 h4 h6
local notation "d" => data (Fin.mk 1 (by omega))
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
local notation "a" => WeierstrassCurve.a₁ (rootShearCurve (W.map (algebraMap R Q)) r)
local notation "c" => algebraMap R Q (Data.b6 d)
local notation "chart" => nodalDepthZeroRetainedChart hπ hm hbound h3 h4 h6 j hj hpos
local notation "s" => coefficientShearGluedStructure hπ data A rA j hj
local notation "b" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))

/-- The full first retained conic for the depth-zero family, at any later depth. -/
def nodalDepthZeroRetainedConic := fiberConicImmersion a c ≫ chart

/-- The whole first incidence line, without imposing a false zero-scale hypothesis. -/
def nodalDepthZeroRetainedLine := fiberIncidenceImmersion a c ≫ chart

instance nodalDepthZeroRetainedConic_mono :
    Mono (nodalDepthZeroRetainedConic hπ hm hbound h3 h4 h6 j hj hpos) :=
  inferInstanceAs (Mono (_ ≫ _))

instance nodalDepthZeroRetainedLine_mono :
    Mono (nodalDepthZeroRetainedLine hπ hm hbound h3 h4 h6 j hj hpos) :=
  inferInstanceAs (Mono (_ ≫ _))

/-- The complete conic keeps the actual integral tangent coefficient specialization. -/
@[reassoc] theorem nodalDepthZeroRetainedConic_structure :
    nodalDepthZeroRetainedConic hπ hm hbound h3 h4 h6 j hj hpos ≫ s =
      conicStructure a c ≫ b := by
  rw [nodalDepthZeroRetainedConic, Category.assoc, nodalDepthZeroRetainedChart_structure,
    ← Category.assoc]
  exact congrArg (fun f => f ≫ b)
    (terminalComponent_algebra_structure (fiberConicMap a c))

/-- The whole incidence line uses the same original tangent coefficient specialization. -/
@[reassoc] theorem nodalDepthZeroRetainedLine_structure :
    nodalDepthZeroRetainedLine hπ hm hbound h3 h4 h6 j hj hpos ≫ s =
      Spec.map (CommRingCat.ofHom (algebraMap Q (Polynomial Q))) ≫ b := by
  rw [nodalDepthZeroRetainedLine, Category.assoc, nodalDepthZeroRetainedChart_structure,
    ← Category.assoc]
  exact congrArg (fun f => f ≫ b)
    (terminalComponent_algebra_structure (fiberIncidenceMap a c))

/-- The line and full conic exhaust exactly the actual first retained chart. -/
theorem nodalDepthZeroRetained_components_cover :
    Set.range (nodalDepthZeroRetainedLine hπ hm hbound h3 h4 h6 j hj hpos) ∪
      Set.range (nodalDepthZeroRetainedConic hπ hm hbound h3 h4 h6 j hj hpos) =
        Set.range chart := by
  ext z
  constructor
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨fiberIncidenceImmersion a c x, rfl⟩
    · exact ⟨fiberConicImmersion a c x, rfl⟩
  · rintro ⟨x, rfl⟩
    rcases fiber_incidence_conic_cover a c x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, rfl⟩

/-- The entire conic incidence open is the full scheme intersection in the integral model. -/
theorem nodalDepthZeroRetainedConicOpen_isPullback :
    IsPullback (fiberConicOpenIso a c).hom (PrincipalOpenTransport.inclusion (conicT a c))
      (PrincipalOpenTransport.inclusion (fiberT a c) ≫ chart)
      (nodalDepthZeroRetainedConic hπ hm hbound h3 h4 h6 j hj hpos) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ chart
    (fiberConicOpen_isPullback a c).cone (fiberConicOpen_isPullback a c).isLimit)

end FLT.Mazur.WeierstrassDividedDepth

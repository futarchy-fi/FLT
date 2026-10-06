/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionFieldPoints
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite geometric fibers of the represented cubic torsion scheme -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- Points of a coefficient pullback are the corresponding points over the original base. -/
def pullbackFieldPointEquiv (X : Over (Spec (.of R)))
    (K : Type u) [Field K] [Algebra R K] :
    {p : Spec (.of K) ⟶ pullback X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) //
      p ≫ pullback.snd _ _ = 𝟙 _} ≃ (pointSource (R := R) K ⟶ X) where
  toFun p := Over.homMk (p.1 ≫ pullback.fst _ _) (by
    change (p.1 ≫ pullback.fst _ _) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R K))
    rw [Category.assoc, pullback.condition, ← Category.assoc, p.2]
    exact Category.id_comp _)
  invFun p := ⟨pullback.lift p.left (𝟙 _) (p.w.trans (Category.id_comp _).symm), by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply pullback.hom_ext <;> simp [p.2]
  right_inv p := by
    apply Over.OverMorphism.ext
    simp

variable (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- After every algebraically closed coefficient-field extension, the nonzero-order
torsion scheme has a finite underlying space, including its nonreduced fibers. -/
theorem finite_torsionModel_geometricFiber
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]
    {n : ℕ} (hn : n ≠ 0) :
    Finite ↥(pullback (torsionModel W n).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) := by
  let X : Scheme := pullback (torsionModel W n).hom
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let f : X ⟶ Spec (.of K) := pullback.snd _ _
  have : IsProper (torsionModel W n).hom := torsionModel_proper W n
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : Finite (pointSource (R := R) K ⟶ torsionModel W n) :=
    finite_torsionModel_fieldPoints W K hn
  have : Finite {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} :=
    Finite.of_equiv _ (pullbackFieldPointEquiv (torsionModel W n) K).symm
  have : Finite (closedPoints X) := Finite.of_equiv _ (pointEquivClosedPoint f)
  have : DiscreteTopology X :=
    JacobsonSpace.discreteTopology (Set.finite_coe_iff.mp inferInstance)
  exact (finite_of_compact_of_discrete : Finite X)

end WeierstrassCurve.CubicCharts

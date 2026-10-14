/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteModificationPointExtension

/-!
# Closed specialization of every original point on the actual modification

The proper extension supplies a closed-fiber point without assuming E₀.
Contraction detects original smooth reduction. In particular an original
torsion point specializing to the actual identity is zero under either
arithmetic rigidity hypothesis, even without assuming smooth reduction first.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (residue A))
local notation "f" => finiteGlobalStructure hπ data j hj

/-- Closed specialization of any original generic point in the whole actual modified fiber. -/
def finitePointSpecialization (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec (.of (ResidueField A)) ⟶ finiteGlobalTensorModel hπ data (ResidueField A) j hj :=
  pullback.lift (𝟙 _) (q ≫ finitePointSection A hπ data j hj P)
    (by rw [Category.assoc, finitePointSection_structure, Category.comp_id, Category.id_comp]; rfl)

/-- The specialized point lies over the identity of the actual residue spectrum. -/
@[reassoc] theorem finitePointSpecialization_structure
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finitePointSpecialization A hπ data j hj P ≫ pullback.fst q f = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The closed point is obtained from the unique integral extension of the original point. -/
@[reassoc] theorem finitePointSpecialization_projection
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finitePointSpecialization A hπ data j hj P ≫ pullback.snd q f =
      q ≫ finitePointSection A hπ data j hj P :=
  pullback.lift_snd _ _ _

/-- Original cubic contraction retains the exact original closed specialization. -/
@[reassoc] theorem finitePointSpecialization_contraction
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finitePointSpecialization A hπ data j hj P ≫
        pullback.snd q f ≫ finiteGlobalContraction hπ data j hj =
      integralPointSpecialization A W P := by
  rw [finitePointSpecialization_projection_assoc, finitePointSection_contraction]
  rfl

/-- The unrestricted construction agrees with the arithmetic E₀ specialization already proved. -/
theorem finitePointSpecialization_e0 (P : ellipticE0 A W) :
    finitePointSpecialization A hπ data j hj P.val = e0FiniteClosedPoint A hπ data j hj P := by
  apply (IsPullback.of_hasPullback q f).hom_ext
  · rw [finitePointSpecialization_structure, e0FiniteClosedPoint_structure]
  · rw [finitePointSpecialization_projection, finitePointSection_e0, e0FiniteClosedPoint_projection]

/-- Equality of actual modified closed points detects original smooth reduction on both sides. -/
theorem finitePointSpecialization_smooth_iff_of_eq
    (P Q : (W.map (algebraMap A K)).toProjective.Point)
    (h : finitePointSpecialization A hπ data j hj P =
      finitePointSpecialization A hπ data j hj Q) :
    SmoothReduction A W P ↔ SmoothReduction A W Q := by
  have he := congrArg (· ≫ pullback.snd q f ≫ finiteGlobalContraction hπ data j hj) h
  rw [finitePointSpecialization_contraction, finitePointSpecialization_contraction] at he
  rw [← integralPointSpecialization_smooth_iff, ← integralPointSpecialization_smooth_iff, he]

/-- Specializing to the actual identity forces membership in the original arithmetic E₀. -/
theorem finitePointSpecialization_eq_zero_smooth
    (P : (W.map (algebraMap A K)).toProjective.Point)
    (h : finitePointSpecialization A hπ data j hj P =
      finitePointSpecialization A hπ data j hj 0) : SmoothReduction A W P :=
  (finitePointSpecialization_smooth_iff_of_eq A hπ data j hj P 0 h).mpr
    (smoothReduction_zero A W)

variable [IsAdicComplete (maximalIdeal A) A]

/-- No nonzero original prime-to-residue torsion point specializes to the actual identity. -/
theorem finitePointSpecialization_torsion_eq_zero
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : m • P = 0)
    (h : finitePointSpecialization A hπ data j hj P =
      finitePointSpecialization A hπ data j hj 0) : P = 0 := by
  let Q : ellipticE0 A W := ⟨P, finitePointSpecialization_eq_zero_smooth A hπ data j hj P h⟩
  have he : e0FiniteClosedPoint A hπ data j hj Q = e0FiniteClosedPoint A hπ data j hj 0 := by
    rw [← finitePointSpecialization_e0, ← finitePointSpecialization_e0]
    exact h
  have hz := e0FiniteClosedPoint_injOn_torsion A hπ data j hj p m hm
    (show m • Q = 0 from Subtype.ext hP) (by simp) he
  exact congrArg (fun x : ellipticE0 A W => x.val) hz

variable [IsDiscreteValuationRing A]

/-- No nonzero original p-torsion specializes to the identity below the ramification bound. -/
theorem finitePointSpecialization_small_ramification_eq_zero
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : p • P = 0)
    (h : finitePointSpecialization A hπ data j hj P =
      finitePointSpecialization A hπ data j hj 0) : P = 0 := by
  let Q : ellipticE0 A W := ⟨P, finitePointSpecialization_eq_zero_smooth A hπ data j hj P h⟩
  have hq : e0FiniteClosedPoint A hπ data j hj Q = e0FiniteClosedPoint A hπ data j hj 0 := by
    rw [← finitePointSpecialization_e0, ← finitePointSpecialization_e0]
    exact h
  have hz := e0FiniteClosedPoint_injOn_small_ramification A hπ data j hj p hp0 he
    (show p • Q = 0 from Subtype.ext hP) (by simp) hq
  exact congrArg (fun x : ellipticE0 A W => x.val) hz

end FLT.Mazur.WeierstrassDividedDepth

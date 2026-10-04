/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.FlatClosedQuotient
public import FLT.Deformations.HardlyRamifiedArithmeticQuotient
public import FLT.Deformations.RepresentationTheory.FlatDiscrete

/-!
# The effective finite-flat quotient of the actual HR arithmetic ring

The residual HR representation proves properness, and the closed-intersection
construction proves finite flatness of every open reduction of the quotient.
No characteristic-zero point or crystalline comparison is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)
local notation "U" => hardlyArithmeticObject O hp hdim ρ hρ
local notation "r" => FramedGaloisRep.ofGL (Subtype.val (hardlyArithmeticLift O hp hdim ρ hρ))
local notation "v" => Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)

/-- The finite-flat defining ideal lies on the previously constructed arithmetic ring. -/
def hardlyFlatIdeal : Ideal U := flatReductionIdeal U v r

/-- Its equations form a closed condition. -/
theorem hardlyFlatIdeal_closed : IsClosed (hardlyFlatIdeal O hp hdim ρ hρ : Set U) :=
  flatReductionIdeal_closed U v r

/-- The residual point is finite flat because it is the original HR representation in its frame. -/
theorem hardlyArithmetic_residual_flat :
    ((r).baseChange (toResidueField U).hom.toRingHom
      (toResidueField U).hom.cont).HasFlatProlongationAt v := by
  have he : (r).baseChange (toResidueField U).hom.toRingHom (toResidueField U).hom.cont =
      ρ.conj (hardlyTwoFrame O hp hdim ρ hρ).symm := by
    apply FramedGaloisRep.GL.injective
    have h := (hardlyArithmeticLift O hp hdim ρ hρ).property
    ext g i j
    have hh := congrArg (fun t : Field.absoluteGaloisGroup ℚ →*
      GL (Fin 2) (residueField (𝓞 := O)) ↦ t g i j) h
    simpa [FramedGaloisRep.ofGL, hardlyTwoFramedResidual,
      Matrix.GeneralLinearGroup.map] using hh
  rw [he]
  exact (GaloisRep.isFlatAt_iff_hasFlatProlongationAt v _).mp
    (hρ.isFlat.conj ρ (hardlyTwoFrame O hp hdim ρ hρ).symm v)

/-- The canonical residual kernel is one of the finite-flat open ideals. -/
theorem hardlyArithmetic_residual_mem :
    RingHom.ker (toResidueField U).hom.toRingHom ∈ flatReductionIdeals U v r := by
  refine ⟨?_, FramedGaloisRep.hasFlatProlongationAt_kernel v r
    (toResidueField U).hom.toRingHom (toResidueField U).hom.cont
    (hardlyArithmetic_residual_flat O hp hdim ρ hρ)⟩
  exact (RingHom.continuous_iff_isOpen_ker).mp (toResidueField U).hom.cont

/-- Residual flatness supplies a proper defining ideal without an added model hypothesis. -/
theorem hardlyFlatIdeal_ne_top : hardlyFlatIdeal O hp hdim ρ hρ ≠ ⊤ :=
  flatReductionIdeal_ne_top U v r (hardlyArithmetic_residual_mem O hp hdim ρ hρ)
    (RingHom.ker_ne_top _)

/-- The actual further quotient imposing flatness at p. -/
def hardlyFlatObject : ProartinianCat O :=
  flatClosedObject U v r (hardlyFlatIdeal_ne_top O hp hdim ρ hρ)

/-- The continuous surjection from the arithmetic HR ring to its flat quotient. -/
def hardlyFlatProjection : U ⟶ hardlyFlatObject O hp hdim ρ hρ :=
  flatClosedProjection U v r (hardlyFlatIdeal_ne_top O hp hdim ρ hρ)

/-- This morphism is an actual quotient projection. -/
theorem hardlyFlatProjection_surjective :
    Function.Surjective (hardlyFlatProjection O hp hdim ρ hρ).hom :=
  Ideal.Quotient.mk_surjective

/-- The same universal arithmetic representation specialized to the finite-flat quotient. -/
def hardlyFlatRepresentation : FramedGaloisRep ℚ (hardlyFlatObject O hp hdim ρ hρ) (Fin 2) :=
  flatClosedRepresentation U v r (hardlyFlatIdeal_ne_top O hp hdim ρ hρ)

/-- Every open coefficient reduction of the actual universal representation is finite flat. -/
theorem hardlyFlatRepresentation_isFlat :
    (hardlyFlatRepresentation O hp hdim ρ hρ).IsFlatAt v :=
  flatClosedRepresentation_isFlat U v r
    ⟨_, hardlyArithmetic_residual_mem O hp hdim ρ hρ⟩
    (hardlyFlatIdeal_ne_top O hp hdim ρ hρ)

/-- The defining ideal detects precisely the finite-flat open reductions of the HR ring. -/
theorem hardlyFlatIdeal_le_iff (J : Ideal U) (hJ : IsOpen (J : Set U)) :
    hardlyFlatIdeal O hp hdim ρ hρ ≤ J ↔
      (GaloisRep.baseChange (U ⧸ J) r).HasFlatProlongationAt v :=
  flatReductionIdeal_le_iff U v r ⟨_, hardlyArithmetic_residual_mem O hp hdim ρ hρ⟩ hJ

end Deformation

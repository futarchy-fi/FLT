/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.DeSmitLenstra.ProfiniteFramedLimit

/-!
# The universal lift over the profinite framed deformation ring

We assemble the compatible universal representations at finite quotients into a continuous
representation over the profinite framed limit and verify its prescribed residue.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Deformation

noncomputable section

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable (n : Type u) [Fintype n] [DecidableEq n]
variable [Finite (ResidueField O)]
variable (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))

open ResidualQuotientIndex

/-- The universal representation at one finite quotient, with its bundled target exposed. -/
def finiteUniversalLift (U : ResidualQuotientIndex O G n rho) :
    Quotient O G n rho U →* GL n (Completion O G n rho U) :=
  universalFramedLift O (Quotient O G n rho U) n (representation O G n rho U)

/-- The matrix formed by the compatible finite-level universal representations. -/
def profiniteUniversalMatrix (g : G) : Matrix n n (ProfiniteFramedLimit O G n rho) :=
  fun i j ↦ ⟨fun U ↦ finiteUniversalLift O G n rho U (QuotientGroup.mk g) i j, by
      intro U V h
      exact transitionMap_universalFramedLift_apply O G n rho h
        (QuotientGroup.mk g) i j⟩

/-- The compatible inverse matrices for the profinite universal representation. -/
def profiniteUniversalInverseMatrix (g : G) :
    Matrix n n (ProfiniteFramedLimit O G n rho) :=
  fun i j ↦ ⟨fun U ↦
    (↑((finiteUniversalLift O G n rho U (QuotientGroup.mk g))⁻¹) :
        Matrix n n (Completion O G n rho U)) i j, by
      intro U V h
      have hmap := congrArg Inv.inv (DFunLike.congr_fun
        (transitionMap_universalFramedLift O G n rho h) (QuotientGroup.mk g))
      have hij := congrArg (fun z : GL n (Completion O G n rho U) ↦
        (z : Matrix n n (Completion O G n rho U)) i j) hmap
      change (transitionRingHom O G n rho U V h)
          ((↑((finiteUniversalLift O G n rho V (QuotientGroup.mk g))⁻¹) :
            Matrix n n (Completion O G n rho V)) i j) =
        (↑((finiteUniversalLift O G n rho U (QuotientGroup.mk g))⁻¹) :
            Matrix n n (Completion O G n rho U)) i j at hij
      exact hij⟩

/-- The unit matrix over the profinite limit attached to an element of `G`. -/
def profiniteUniversalElement (g : G) : GL n (ProfiniteFramedLimit O G n rho) where
  val := profiniteUniversalMatrix O G n rho g
  inv := profiniteUniversalInverseMatrix O G n rho g
  val_inv := by
    unfold ProfiniteFramedLimit
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    funext U
    change (RingHom.mapMatrix (profiniteFramedLimitComponent O G n rho U))
        (profiniteUniversalMatrix O G n rho g *
          profiniteUniversalInverseMatrix O G n rho g) i j =
      (RingHom.mapMatrix (profiniteFramedLimitComponent O G n rho U)) 1 i j
    rw [map_mul, map_one]
    change ((↑(finiteUniversalLift O G n rho U (QuotientGroup.mk g)) :
      Matrix n n (Completion O G n rho U)) *
      (↑((finiteUniversalLift O G n rho U (QuotientGroup.mk g))⁻¹) :
        Matrix n n (Completion O G n rho U))) i j =
          (1 : Matrix n n (Completion O G n rho U)) i j
    exact congrFun (congrFun
      (Units.val_inv (finiteUniversalLift O G n rho U (QuotientGroup.mk g))) i) j
  inv_val := by
    unfold ProfiniteFramedLimit
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    funext U
    change (RingHom.mapMatrix (profiniteFramedLimitComponent O G n rho U))
        (profiniteUniversalInverseMatrix O G n rho g *
          profiniteUniversalMatrix O G n rho g) i j =
      (RingHom.mapMatrix (profiniteFramedLimitComponent O G n rho U)) 1 i j
    rw [map_mul, map_one]
    change ((↑((finiteUniversalLift O G n rho U (QuotientGroup.mk g))⁻¹) :
        Matrix n n (Completion O G n rho U)) *
      (↑(finiteUniversalLift O G n rho U (QuotientGroup.mk g)) :
        Matrix n n (Completion O G n rho U))) i j =
          (1 : Matrix n n (Completion O G n rho U)) i j
    exact congrFun (congrFun
      (Units.inv_val (finiteUniversalLift O G n rho U (QuotientGroup.mk g))) i) j

/-- The universal group representation over the profinite framed limit. -/
def profiniteUniversalLift : G →* GL n (ProfiniteFramedLimit O G n rho) where
  toFun := profiniteUniversalElement O G n rho
  map_one' := by
    unfold ProfiniteFramedLimit
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    funext U
    change (RingHom.mapMatrix (profiniteFramedLimitComponent O G n rho U))
        (profiniteUniversalElement O G n rho 1).val i j =
      (RingHom.mapMatrix (profiniteFramedLimitComponent O G n rho U)) 1 i j
    rw [map_one]
    change (↑(finiteUniversalLift O G n rho U 1) :
      Matrix n n (Completion O G n rho U)) i j =
        (1 : Matrix n n (Completion O G n rho U)) i j
    exact congrArg (fun z : GL n (Completion O G n rho U) ↦
      (z : Matrix n n (Completion O G n rho U)) i j)
      (map_one (finiteUniversalLift O G n rho U))
  map_mul' g h := by
    unfold ProfiniteFramedLimit
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    funext U
    change (RingHom.mapMatrix (profiniteFramedLimitComponent O G n rho U))
        (profiniteUniversalElement O G n rho (g * h)).val i j =
      (RingHom.mapMatrix (profiniteFramedLimitComponent O G n rho U))
        ((profiniteUniversalElement O G n rho g).val *
          (profiniteUniversalElement O G n rho h).val) i j
    rw [map_mul]
    change (↑(finiteUniversalLift O G n rho U (QuotientGroup.mk (g * h))) :
      Matrix n n (Completion O G n rho U)) i j =
      ((↑(finiteUniversalLift O G n rho U (QuotientGroup.mk g)) :
          Matrix n n (Completion O G n rho U)) *
        (↑(finiteUniversalLift O G n rho U (QuotientGroup.mk h)) :
          Matrix n n (Completion O G n rho U))) i j
    exact congrArg (fun z : GL n (Completion O G n rho U) ↦
      (z : Matrix n n (Completion O G n rho U)) i j)
      (map_mul (finiteUniversalLift O G n rho U)
        (QuotientGroup.mk g) (QuotientGroup.mk h))

omit [TotallyDisconnectedSpace G] in
lemma profiniteUniversalMatrix_continuous :
    Continuous (profiniteUniversalMatrix O G n rho) := by
  apply continuous_matrix
  intro i j
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro U
  let _ : DiscreteTopology (Quotient O G n rho U) :=
    QuotientGroup.discreteTopology (subgroup O G n rho U).isOpen
  exact (continuous_of_discreteTopology : Continuous (fun x : Quotient O G n rho U ↦
    finiteUniversalLift O G n rho U x i j)).comp continuous_quotient_mk'

omit [TotallyDisconnectedSpace G] in
lemma profiniteUniversalInverseMatrix_continuous :
    Continuous (profiniteUniversalInverseMatrix O G n rho) := by
  apply continuous_matrix
  intro i j
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro U
  let _ : DiscreteTopology (Quotient O G n rho U) :=
    QuotientGroup.discreteTopology (subgroup O G n rho U).isOpen
  exact (continuous_of_discreteTopology : Continuous (fun x : Quotient O G n rho U ↦
    (↑((finiteUniversalLift O G n rho U x)⁻¹) :
      Matrix n n (Completion O G n rho U)) i j)).comp continuous_quotient_mk'

omit [TotallyDisconnectedSpace G] in
lemma profiniteUniversalLift_continuous :
    Continuous (profiniteUniversalLift O G n rho) := by
  rw [Units.continuous_iff]
  exact ⟨profiniteUniversalMatrix_continuous O G n rho,
    profiniteUniversalInverseMatrix_continuous O G n rho⟩

/-- The continuous universal representation carried by the profinite framed limit. -/
def profiniteUniversalContinuousLift :
    G →ₜ* GL n (ProfiniteFramedLimit O G n rho) :=
  ⟨profiniteUniversalLift O G n rho, profiniteUniversalLift_continuous O G n rho⟩

/-- A projection from the profinite framed limit, as a morphism of proartinian algebras. -/
def profiniteFramedLimitComponentHom (U : ResidualQuotientIndex O G n rho) :
    profiniteFramedLimitObject O G n rho ⟶ Completion O G n rho U where
  hom :=
    { toAlgHom :=
        { toRingHom := profiniteFramedLimitComponent O G n rho U
          commutes' := fun o ↦ algebraMap_profiniteFramedLimit_apply O G n rho o U }
      cont := profiniteFramedLimitComponent_continuous O G n rho U }

/-- A continuous framed lift is a continuous representation with prescribed residue. -/
def IsContinuousFramedLift (S : ProartinianCat O) (tau : G →ₜ* GL n S) : Prop :=
  (Matrix.GeneralLinearGroup.map
    (ProartinianCat.toResidueField S).hom.toRingHom).comp tau.toMonoidHom = rho.toMonoidHom

omit [TotallyDisconnectedSpace G] in
lemma profiniteUniversalContinuousLift_isFramedLift :
    IsContinuousFramedLift O G n rho (profiniteFramedLimitObject O G n rho)
      (profiniteUniversalContinuousLift O G n rho) := by
  unfold IsContinuousFramedLift
  ext g i j
  let U := kernelIndex O G n rho
  have hres : profiniteFramedLimitComponentHom O G n rho U ≫
      ProartinianCat.toResidueField (Completion O G n rho U) =
        ProartinianCat.toResidueField (profiniteFramedLimitObject O G n rho) :=
    Subsingleton.elim _ _
  rw [← hres]
  change (ProartinianCat.toResidueField (Completion O G n rho U)).hom
      ((profiniteFramedLimitComponent O G n rho U)
        ((profiniteUniversalMatrix O G n rho g) i j)) = rho g i j
  change (ProartinianCat.toResidueField (Completion O G n rho U)).hom
      ((finiteUniversalLift O G n rho U (QuotientGroup.mk g) :
        GL n (Completion O G n rho U)) i j) = rho g i j
  have hf := congrArg
    (fun f : Quotient O G n rho U →* GL n (ProartinianCat.residueField (𝓞 := O)) ↦
      f (QuotientGroup.mk g) i j)
    (universalFramedLift_isFramedLift O (Quotient O G n rho U) n
      (representation O G n rho U))
  change (ProartinianCat.toResidueField (Completion O G n rho U)).hom
      ((finiteUniversalLift O G n rho U (QuotientGroup.mk g) :
        GL n (Completion O G n rho U)) i j) =
      representation O G n rho U (QuotientGroup.mk g) i j at hf
  rw [representation_mk] at hf
  exact hf

end

end Deformation

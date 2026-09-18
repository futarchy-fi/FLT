/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.DeSmitLenstra.ProfiniteFramedLimit
public import FLT.Deformations.ProartinianQuotients

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
variable (n : Type) [Fintype n] [DecidableEq n]
variable [Finite (ResidueField O)]
variable (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))

open ResidualQuotientIndex

/-- Restrict framed coordinate functions along a residual finite quotient. -/
noncomputable def residualQuotientRepresentationMap
    (U : ResidualQuotientIndex O G n rho) :
    FramedRepresentationRing O G n →ₐ[O]
      FramedRepresentationRing O (Quotient O G n rho U) n :=
  FramedRepresentationRing.ofRepresentation
    ((universalRepresentation O (Quotient O G n rho U) n).comp
      (QuotientGroup.mk' (subgroup O G n rho U).toSubgroup))

omit [IsNoetherianRing O] [CompactSpace G]
  [TotallyDisconnectedSpace G] [Finite (ResidueField O)] in
lemma residualQuotientRepresentationMap_quotient
    (U : ResidualQuotientIndex O G n rho)
    (p : FramedRepresentationPolynomial O G n) :
    residualQuotientRepresentationMap O G n rho U
        (framedRepresentationQuotient O G n p) =
      framedRepresentationQuotient O (Quotient O G n rho U) n
        (MvPolynomial.rename
          (fun x : G × (n × n) ↦ (QuotientGroup.mk x.1, x.2)) p) := by
  change ((residualQuotientRepresentationMap O G n rho U).comp
      (framedRepresentationQuotient O G n)) p =
    ((framedRepresentationQuotient O (Quotient O G n rho U) n).comp
      (MvPolynomial.rename
        (fun x : G × (n × n) ↦ (QuotientGroup.mk x.1, x.2)))) p
  congr 1
  apply MvPolynomial.algHom_ext
  rintro ⟨g, i, j⟩
  simp [residualQuotientRepresentationMap, FramedRepresentationRing.ofRepresentation,
    universalRepresentation, universalRepresentationMatrix,
    framedRepresentationQuotient, RingQuot.liftAlgHom_mkAlgHom_apply]

omit [IsNoetherianRing O] [CompactSpace G]
  [TotallyDisconnectedSpace G] [Finite (ResidueField O)] in
lemma residualQuotientRepresentationMap_surjective
    (U : ResidualQuotientIndex O G n rho) :
    Function.Surjective (residualQuotientRepresentationMap O G n rho U) := by
  intro y
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective O
    (FramedRepresentationRelation O (Quotient O G n rho U) n) y
  obtain ⟨p, hp⟩ := MvPolynomial.rename_surjective
    (fun x : G × (n × n) ↦ (QuotientGroup.mk x.1, x.2))
    (fun ⟨g, i, j⟩ ↦ by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (subgroup O G n rho U).toSubgroup g
      exact ⟨(g, (i, j)), rfl⟩) p
  exact ⟨framedRepresentationQuotient O G n p,
    (residualQuotientRepresentationMap_quotient O G n rho U p).trans (congrArg _ hp)⟩

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

/-- The coordinate-algebra map generated by the profinite universal representation. -/
noncomputable def profiniteFramedRepresentationMap :
    FramedRepresentationRing O G n →ₐ[O] ProfiniteFramedLimit O G n rho :=
  FramedRepresentationRing.ofRepresentation (profiniteUniversalLift O G n rho)

omit [TotallyDisconnectedSpace G] in
lemma profiniteFramedRepresentationMap_component
    (U : ResidualQuotientIndex O G n rho) (a : FramedRepresentationRing O G n) :
    profiniteFramedLimitComponent O G n rho U
        (profiniteFramedRepresentationMap O G n rho a) =
      framedRepresentationToCompletion O (Quotient O G n rho U) n
        (representation O G n rho U)
        (residualQuotientRepresentationMap O G n rho U a) := by
  let lhs : FramedRepresentationRing O G n →ₐ[O] Completion O G n rho U :=
    (profiniteFramedLimitComponentHom O G n rho U).hom.toAlgHom.comp
      (profiniteFramedRepresentationMap O G n rho)
  let rhs : FramedRepresentationRing O G n →ₐ[O] Completion O G n rho U :=
    (framedRepresentationToCompletion O (Quotient O G n rho U) n
      (representation O G n rho U)).comp
        (residualQuotientRepresentationMap O G n rho U)
  have h : lhs = rhs := by
    apply RingQuot.ringQuot_ext'
    apply MvPolynomial.algHom_ext
    rintro ⟨g, i, j⟩
    change profiniteFramedLimitComponent O G n rho U
        (profiniteFramedRepresentationMap O G n rho
          (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j))))) =
      framedRepresentationToCompletion O (Quotient O G n rho U) n
        (representation O G n rho U)
        (residualQuotientRepresentationMap O G n rho U
          (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j)))))
    unfold profiniteFramedRepresentationMap residualQuotientRepresentationMap
    rw [FramedRepresentationRing.ofRepresentation_generator,
      FramedRepresentationRing.ofRepresentation_generator]
    rfl
  exact DFunLike.congr_fun h a

omit [TotallyDisconnectedSpace G] in
/-- The global framed coordinate functions are dense in the profinite framed limit. -/
lemma profiniteFramedRepresentationMap_denseRange :
    DenseRange (profiniteFramedRepresentationMap O G n rho) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro V ⟨s, hsOpen, hsV⟩ ⟨⟨x, hx⟩, hxs⟩
  have hxs' : x ∈ s := by
    change (⟨x, hx⟩ : ProfiniteFramedLimit O G n rho) ∈ Subtype.val ⁻¹' s
    rw [hsV]
    exact hxs
  rcases (isOpen_pi_iff.mp hsOpen) x hxs' with ⟨J, v, hJmem, hJsub⟩
  let _ : IsDirectedOrder (ResidualQuotientIndex O G n rho) :=
    ⟨ResidualQuotientIndex.directed O G n rho⟩
  obtain ⟨W, hW⟩ := J.finite_toSet.bddAbove
  let t : Set (Completion O G n rho W) := ⋂ a : J,
    (transitionRingHom O G n rho a.1 W (hW a.2)) ⁻¹' v a.1
  have htOpen : IsOpen t := isOpen_iInter_of_finite fun a : J ↦
    (hJmem a.1 a.2).1.preimage
      (ResidualQuotientIndex.transitionMap O G n rho (hW a.2)).hom.cont
  have hxt : x W ∈ t := by
    apply Set.mem_iInter.mpr
    intro a
    change transitionRingHom O G n rho a.1 W (hW a.2) (x W) ∈ v a.1
    rw [hx a.1 W (hW a.2)]
    exact (hJmem a.1 a.2).2
  have hDenseW : DenseRange (fun a : FramedRepresentationRing O G n ↦
      profiniteFramedLimitComponent O G n rho W
        (profiniteFramedRepresentationMap O G n rho a)) := by
    rw [show (fun a : FramedRepresentationRing O G n ↦
        profiniteFramedLimitComponent O G n rho W
          (profiniteFramedRepresentationMap O G n rho a)) =
      (fun a ↦ framedRepresentationToCompletionObject O (Quotient O G n rho W) n
        (representation O G n rho W)
          (residualQuotientRepresentationMap O G n rho W a)) by
        funext a
        exact profiniteFramedRepresentationMap_component O G n rho W a]
    change DenseRange ((framedRepresentationToCompletionObject O
      (Quotient O G n rho W) n (representation O G n rho W)) ∘
        residualQuotientRepresentationMap O G n rho W)
    rw [DenseRange, Set.range_comp,
      (residualQuotientRepresentationMap_surjective O G n rho W).range_eq,
      Set.image_univ]
    exact framedRepresentationToCompletionObject_denseRange O
      (Quotient O G n rho W) n (representation O G n rho W)
  rw [DenseRange, dense_iff_inter_open] at hDenseW
  obtain ⟨z, hzt, a, ha⟩ := hDenseW t htOpen ⟨x W, hxt⟩
  refine ⟨profiniteFramedRepresentationMap O G n rho a, ?_, a, rfl⟩
  rw [← hsV]
  apply hJsub
  intro U hU
  have hzU : transitionRingHom O G n rho U W (hW hU) z ∈ v U :=
    Set.mem_iInter.mp hzt ⟨U, hU⟩
  rw [← ha] at hzU
  rw [show transitionRingHom O G n rho U W (hW hU)
      (profiniteFramedLimitComponent O G n rho W
        (profiniteFramedRepresentationMap O G n rho a)) =
    profiniteFramedLimitComponent O G n rho U
      (profiniteFramedRepresentationMap O G n rho a) from
        (profiniteFramedRepresentationMap O G n rho a).prop U W (hW hU)] at hzU
  exact hzU

/-- Continuous framed lifts to a proartinian algebra. -/
def ContinuousFramedLifts (S : ProartinianCat O) :=
  { tau : G →ₜ* GL n S // IsContinuousFramedLift O G n rho S tau }

/-- A morphism from the profinite framed limit specializes its universal lift. -/
noncomputable def profiniteFramedLimitHomToLift (S : ProartinianCat O)
    (f : profiniteFramedLimitObject O G n rho ⟶ S) :
    ContinuousFramedLifts O G n rho S := by
  let tau : G →ₜ* GL n S :=
    (Units.mapₜ f.hom.mapMatrix.toContinuousMonoidHom).comp
      (profiniteUniversalContinuousLift O G n rho)
  refine ⟨tau, ?_⟩
  unfold IsContinuousFramedLift
  ext g i j
  have hres : f ≫ ProartinianCat.toResidueField S =
      ProartinianCat.toResidueField (profiniteFramedLimitObject O G n rho) :=
    Subsingleton.elim _ _
  change (ProartinianCat.toResidueField S).hom
      (f.hom ((profiniteUniversalMatrix O G n rho g) i j)) = rho g i j
  change (f ≫ ProartinianCat.toResidueField S).hom
      ((profiniteUniversalMatrix O G n rho g) i j) = rho g i j
  rw [hres]
  have hu := congrArg
    (fun r : G →* GL n (ProartinianCat.residueField (𝓞 := O)) ↦ r g i j)
    (profiniteUniversalContinuousLift_isFramedLift O G n rho)
  exact hu

section LiftToHom

variable (S : ProartinianCat O) (tau : ContinuousFramedLifts O G n rho S)

/-- Reduce a continuous framed lift modulo a proper open ideal. -/
noncomputable def quotientContinuousLift (I : ProartinianCat.OpenIdeal S) :
    G →ₜ* GL n (ProartinianCat.openIdealQuotient S I) :=
  (Units.mapₜ
    ((ProartinianCat.openIdealQuotientHom S I).hom.mapMatrix.toContinuousMonoidHom)).comp tau.1

omit [IsNoetherianRing O] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
lemma quotientContinuousLift_isFramedLift (I : ProartinianCat.OpenIdeal S) :
    IsContinuousFramedLift O G n rho (ProartinianCat.openIdealQuotient S I)
      (quotientContinuousLift O G n (rho := rho) (S := S) tau I) := by
  unfold IsContinuousFramedLift
  ext g i j
  have hres : ProartinianCat.openIdealQuotientHom S I ≫
      ProartinianCat.toResidueField (ProartinianCat.openIdealQuotient S I) =
      ProartinianCat.toResidueField S :=
    Subsingleton.elim _ _
  change (ProartinianCat.toResidueField
      (ProartinianCat.openIdealQuotient S I)).hom
      ((ProartinianCat.openIdealQuotientHom S I).hom (tau.1 g i j)) = rho g i j
  change (ProartinianCat.openIdealQuotientHom S I ≫
      ProartinianCat.toResidueField (ProartinianCat.openIdealQuotient S I)).hom
      (tau.1 g i j) = rho g i j
  rw [hres]
  exact congrArg
    (fun r : G →* GL n (ProartinianCat.residueField (𝓞 := O)) ↦ r g i j) tau.2

/-- The finite residual quotient detected by reducing a continuous lift modulo an open ideal. -/
noncomputable def quotientLiftIndex (I : ProartinianCat.OpenIdeal S) :
    ResidualQuotientIndex O G n rho := by
  let : DiscreteTopology (ProartinianCat.openIdealQuotient S I) := by
    change DiscreteTopology (S ⧸ ProartinianCat.OpenIdeal.ideal I)
    exact QuotientAddGroup.discreteTopology (ProartinianCat.OpenIdeal.isOpen I)
  let : DiscreteTopology (GL n (ProartinianCat.openIdealQuotient S I)) := inferInstance
  exact OrderDual.toDual ⟨
    { toSubgroup :=
        (quotientContinuousLift O G n (rho := rho) (S := S) tau I).toMonoidHom.ker
      isOpen' := MonoidHom.continuous_iff_isOpen_ker.mp
        (quotientContinuousLift O G n (rho := rho) (S := S) tau I).continuous
      isNormal' := inferInstance }, by
    intro g hg
    change rho g = 1
    change quotientContinuousLift O G n (rho := rho) (S := S) tau I g = 1 at hg
    have h := congrArg
      (fun r : G →* GL n (ProartinianCat.residueField (𝓞 := O)) ↦ r g)
      (quotientContinuousLift_isFramedLift O G n rho S tau I)
    change Matrix.GeneralLinearGroup.map
      (ProartinianCat.toResidueField (ProartinianCat.openIdealQuotient S I)).hom.toRingHom
      (quotientContinuousLift O G n (rho := rho) (S := S) tau I g) = rho g at h
    rw [hg, map_one] at h
    exact h.symm ⟩

/-- The reduced lift descended to its finite quotient. -/
noncomputable def quotientLiftRepresentation (I : ProartinianCat.OpenIdeal S) :
    ResidualQuotientIndex.Quotient O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S I) →* GL n
      (ProartinianCat.openIdealQuotient S I) :=
  QuotientGroup.lift
    (ResidualQuotientIndex.subgroup O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S I)).toSubgroup
    (quotientContinuousLift O G n (rho := rho) (S := S) tau I).toMonoidHom le_rfl

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
lemma quotientLiftRepresentation_mk (I : ProartinianCat.OpenIdeal S) (g : G) :
    quotientLiftRepresentation O G n (rho := rho) (tau := tau) S I (QuotientGroup.mk g) =
      quotientContinuousLift O G n (rho := rho) (S := S) tau I g :=
  rfl

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G] in
lemma quotientLiftRepresentation_isFramedLift (I : ProartinianCat.OpenIdeal S) :
    IsFramedLift O (ResidualQuotientIndex.Quotient O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S I)) n
      (ResidualQuotientIndex.representation O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S I))
      (ProartinianCat.openIdealQuotient S I)
      (quotientLiftRepresentation O G n (rho := rho) (tau := tau) S I) := by
  unfold IsFramedLift
  apply (MonoidHom.cancel_right (QuotientGroup.mk'_surjective
    (ResidualQuotientIndex.subgroup O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S I)).toSubgroup)).mp
  ext g i j
  change (ProartinianCat.toResidueField
      (ProartinianCat.openIdealQuotient S I)).hom
      (quotientContinuousLift O G n (rho := rho) (S := S) tau I g i j) = rho g i j
  exact congrArg
    (fun r : G →* GL n (ProartinianCat.residueField (𝓞 := O)) ↦ r g i j)
    (quotientContinuousLift_isFramedLift O G n rho S tau I)

/-- The finite-level universal map associated to a reduced continuous lift. -/
noncomputable def quotientCompletionMap (I : ProartinianCat.OpenIdeal S) :
    Completion O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S I) →A[O]
      ProartinianCat.openIdealQuotient S I :=
  (framedCompletionLiftToHom O
    (ResidualQuotientIndex.Quotient O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S I)) n
    (ResidualQuotientIndex.representation O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S I))
    (ProartinianCat.openIdealQuotient S I)
    ⟨quotientLiftRepresentation O G n (rho := rho) (tau := tau) S I,
      quotientLiftRepresentation_isFramedLift O G n rho S tau I⟩).hom

/-- The finite-level universal map, bundled in the proartinian category. -/
noncomputable def quotientCompletionHom (I : ProartinianCat.OpenIdeal S) :
    Completion O G n rho (quotientLiftIndex O G n (rho := rho) (tau := tau) S I) ⟶
      ProartinianCat.openIdealQuotient S I where
  hom := quotientCompletionMap O G n rho S tau I

omit [TotallyDisconnectedSpace G] in
lemma quotientCompletionMap_universalFramedLift (I : ProartinianCat.OpenIdeal S) :
    (Matrix.GeneralLinearGroup.map
      (quotientCompletionMap O G n rho S tau I).toRingHom).comp
      (finiteUniversalLift O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S I)) =
      quotientLiftRepresentation O G n (rho := rho) (tau := tau) S I :=
  framedCompletionMap_universalFramedLift O _ n _ _ _
    (quotientLiftRepresentation_isFramedLift O G n rho S tau I)

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G] in
lemma quotientLiftIndex_mono {I J : ProartinianCat.OpenIdeal S} (h : I ≤ J) :
    quotientLiftIndex O G n (rho := rho) (tau := tau) S I ≤
      quotientLiftIndex O G n (rho := rho) (tau := tau) S J := by
  change (quotientContinuousLift O G n (rho := rho) (S := S) tau J).toMonoidHom.ker ≤
    (quotientContinuousLift O G n (rho := rho) (S := S) tau I).toMonoidHom.ker
  intro g hg
  change quotientContinuousLift O G n (rho := rho) (S := S) tau I g = 1
  change quotientContinuousLift O G n (rho := rho) (S := S) tau J g = 1 at hg
  let q := (ProartinianCat.openIdealQuotientTransitionHom S I J h).hom.toRingHom
  have hmap : quotientContinuousLift O G n (rho := rho) (S := S) tau I g =
      Matrix.GeneralLinearGroup.map q
        (quotientContinuousLift O G n (rho := rho) (S := S) tau J g) := by
    apply Units.ext
    ext i j
    exact (Ideal.Quotient.factor_mk (ProartinianCat.OpenIdeal.ideal_le_ideal h)
      (tau.1 g i j)).symm
  rw [hmap, hg, map_one]

/-- The map from the profinite limit to one open-ideal quotient of a target lift. -/
noncomputable def quotientProfiniteMap (I : ProartinianCat.OpenIdeal S) :
    ProfiniteFramedLimit O G n rho →A[O] ProartinianCat.openIdealQuotient S I :=
  (quotientCompletionMap O G n rho S tau I).comp
    (profiniteFramedLimitComponentHom O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S I)).hom

/-- A reduced lift pulled back from a coarser group quotient to a finer one. -/
noncomputable def refinedQuotientLift {I J : ProartinianCat.OpenIdeal S} (h : I ≤ J) :
    ResidualQuotientIndex.Quotient O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S J) →* GL n
        (ProartinianCat.openIdealQuotient S I) :=
  (quotientLiftRepresentation O G n (rho := rho) (tau := tau) S I).comp
    (ResidualQuotientIndex.quotientMap O G n rho
      (quotientLiftIndex_mono O G n rho S tau h))

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G] in
lemma refinedQuotientLift_isFramedLift {I J : ProartinianCat.OpenIdeal S} (h : I ≤ J) :
    IsFramedLift O
      (ResidualQuotientIndex.Quotient O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S J)) n
      (ResidualQuotientIndex.representation O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S J))
      (ProartinianCat.openIdealQuotient S I) (refinedQuotientLift O G n rho S tau h) := by
  unfold IsFramedLift
  apply (MonoidHom.cancel_right (QuotientGroup.mk'_surjective
    (ResidualQuotientIndex.subgroup O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S J)).toSubgroup)).mp
  ext g i j
  change (ProartinianCat.toResidueField
    (ProartinianCat.openIdealQuotient S I)).hom
      (quotientContinuousLift O G n (rho := rho) (S := S) tau I g i j) = rho g i j
  exact congrArg
    (fun r : G →* GL n (ProartinianCat.residueField (𝓞 := O)) ↦ r g i j)
    (quotientContinuousLift_isFramedLift O G n rho S tau I)

omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G] in
lemma quotientLiftRepresentation_compatible {I J : ProartinianCat.OpenIdeal S} (h : I ≤ J) :
    (Matrix.GeneralLinearGroup.map
      (ProartinianCat.openIdealQuotientTransitionHom S I J h).hom.toRingHom).comp
        (quotientLiftRepresentation O G n (rho := rho) (tau := tau) S J) =
      refinedQuotientLift O G n rho S tau h := by
  apply (MonoidHom.cancel_right (QuotientGroup.mk'_surjective
    (ResidualQuotientIndex.subgroup O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S J)).toSubgroup)).mp
  ext g i j
  exact Ideal.Quotient.factor_mk (ProartinianCat.OpenIdeal.ideal_le_ideal h)
    (tau.1 g i j)

/-- The finite-level map obtained by first changing the group quotient. -/
noncomputable def quotientCompletionLeft {I J : ProartinianCat.OpenIdeal S} (h : I ≤ J) :
    Completion O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S J) ⟶
      ProartinianCat.openIdealQuotient S I :=
  ResidualQuotientIndex.transitionMap O G n rho
      (quotientLiftIndex_mono O G n rho S tau h) ≫
    quotientCompletionHom O G n rho S tau I

/-- The finite-level map obtained by first changing the coefficient quotient. -/
noncomputable def quotientCompletionRight {I J : ProartinianCat.OpenIdeal S} (h : I ≤ J) :
    Completion O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S J) ⟶
      ProartinianCat.openIdealQuotient S I :=
  quotientCompletionHom O G n rho S tau J ≫
    ProartinianCat.openIdealQuotientTransitionHom S I J h

omit [TotallyDisconnectedSpace G] in
lemma quotientCompletionLeft_universal {I J : ProartinianCat.OpenIdeal S} (h : I ≤ J) :
    (Matrix.GeneralLinearGroup.map
      (quotientCompletionLeft O G n rho S tau h).hom.toRingHom).comp
      (finiteUniversalLift O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S J)) =
      refinedQuotientLift O G n rho S tau h := by
  unfold quotientCompletionLeft
  simp only [ProartinianCat.hom_comp, ContinuousAlgHom.coe_comp]
  change (Matrix.GeneralLinearGroup.map
    ((quotientCompletionMap O G n rho S tau I).toRingHom.comp
      (ResidualQuotientIndex.transitionMap O G n rho
        (quotientLiftIndex_mono O G n rho S tau h)).hom.toRingHom)).comp _ = _
  rw [Matrix.GeneralLinearGroup.map_comp]
  apply DFunLike.ext _ _
  intro x
  simp only [MonoidHom.comp_apply]
  have hx := DFunLike.congr_fun
    (ResidualQuotientIndex.transitionMap_universalFramedLift O G n rho
      (quotientLiftIndex_mono O G n rho S tau h)) x
  change Matrix.GeneralLinearGroup.map
    (ResidualQuotientIndex.transitionMap O G n rho
      (quotientLiftIndex_mono O G n rho S tau h)).hom.toRingHom
    (finiteUniversalLift O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S J) x) =
    ResidualQuotientIndex.transitionLift O G n rho
      (quotientLiftIndex_mono O G n rho S tau h) x at hx
  rw [hx]
  unfold ResidualQuotientIndex.transitionLift refinedQuotientLift
  exact DFunLike.congr_fun
    (quotientCompletionMap_universalFramedLift O G n rho S tau I)
    (ResidualQuotientIndex.quotientMap O G n rho
      (quotientLiftIndex_mono O G n rho S tau h) x)

omit [TotallyDisconnectedSpace G] in
lemma quotientCompletionRight_universal {I J : ProartinianCat.OpenIdeal S} (h : I ≤ J) :
    (Matrix.GeneralLinearGroup.map
      (quotientCompletionRight O G n rho S tau h).hom.toRingHom).comp
      (finiteUniversalLift O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S J)) =
      refinedQuotientLift O G n rho S tau h := by
  unfold quotientCompletionRight
  simp only [ProartinianCat.hom_comp, ContinuousAlgHom.coe_comp]
  change (Matrix.GeneralLinearGroup.map
    ((ProartinianCat.openIdealQuotientTransitionHom S I J h).hom.toRingHom.comp
      (quotientCompletionMap O G n rho S tau J).toRingHom)).comp _ = _
  rw [Matrix.GeneralLinearGroup.map_comp]
  apply DFunLike.ext _ _
  intro x
  simp only [MonoidHom.comp_apply]
  have hx := DFunLike.congr_fun
    (quotientCompletionMap_universalFramedLift O G n rho S tau J) x
  change Matrix.GeneralLinearGroup.map
    (quotientCompletionMap O G n rho S tau J).toRingHom
      (finiteUniversalLift O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S J) x) =
    quotientLiftRepresentation O G n (rho := rho) (tau := tau) S J x at hx
  rw [hx]
  exact DFunLike.congr_fun (quotientLiftRepresentation_compatible O G n rho S tau h) x

omit [TotallyDisconnectedSpace G] in
lemma quotientCompletionMap_compatible {I J : ProartinianCat.OpenIdeal S} (h : I ≤ J) :
    ResidualQuotientIndex.transitionMap O G n rho
        (quotientLiftIndex_mono O G n rho S tau h) ≫
      quotientCompletionHom O G n rho S tau I =
    quotientCompletionHom O G n rho S tau J ≫
      ProartinianCat.openIdealQuotientTransitionHom S I J h := by
  change quotientCompletionLeft O G n rho S tau h =
    quotientCompletionRight O G n rho S tau h
  have hleft := framedCompletionHom_unique O
    (ResidualQuotientIndex.Quotient O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S J)) n
    (ResidualQuotientIndex.representation O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S J))
    (ProartinianCat.openIdealQuotient S I)
    (refinedQuotientLift O G n rho S tau h)
    (refinedQuotientLift_isFramedLift O G n rho S tau h)
    (quotientCompletionLeft O G n rho S tau h)
    (quotientCompletionLeft_universal O G n rho S tau h)
  have hright := framedCompletionHom_unique O
    (ResidualQuotientIndex.Quotient O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S J)) n
    (ResidualQuotientIndex.representation O G n rho
      (quotientLiftIndex O G n (rho := rho) (tau := tau) S J))
    (ProartinianCat.openIdealQuotient S I)
    (refinedQuotientLift O G n rho S tau h)
    (refinedQuotientLift_isFramedLift O G n rho S tau h)
    (quotientCompletionRight O G n rho S tau h)
    (quotientCompletionRight_universal O G n rho S tau h)
  exact hleft.trans hright.symm

omit [TotallyDisconnectedSpace G] in
lemma quotientProfiniteMap_compatible (I J : ProartinianCat.OpenIdeal S) (h : I ≤ J)
    (x : ProfiniteFramedLimit O G n rho) :
    ProartinianCat.openIdealTransition S I J h (quotientProfiniteMap O G n rho S tau J x) =
      quotientProfiniteMap O G n rho S tau I x := by
  have hx := DFunLike.congr_fun
    (congrArg ProartinianCat.Hom.hom
      (quotientCompletionMap_compatible O G n rho S tau h))
    (x.val (quotientLiftIndex O G n (rho := rho) (tau := tau) S J))
  simp only [ProartinianCat.comp_apply] at hx
  change quotientCompletionMap O G n rho S tau I
      ((ResidualQuotientIndex.transitionMap O G n rho
        (quotientLiftIndex_mono O G n rho S tau h)).hom
        (x.val (quotientLiftIndex O G n (rho := rho) (tau := tau) S J))) =
    (ProartinianCat.openIdealQuotientTransitionHom S I J h).hom
      (quotientCompletionMap O G n rho S tau J
        (x.val (quotientLiftIndex O G n (rho := rho) (tau := tau) S J))) at hx
  rw [show (ResidualQuotientIndex.transitionMap O G n rho
      (quotientLiftIndex_mono O G n rho S tau h)).hom
      (x.val (quotientLiftIndex O G n (rho := rho) (tau := tau) S J)) =
    x.val (quotientLiftIndex O G n (rho := rho) (tau := tau) S I) from
      x.prop _ _ (quotientLiftIndex_mono O G n rho S tau h)] at hx
  exact hx.symm

/-- Assemble the finite quotient maps into a ring map to the target proartinian algebra. -/
noncomputable def profiniteFramedLimitLiftRingHom :
    ProfiniteFramedLimit O G n rho →+* S :=
  ProartinianCat.liftCompatibleQuotients S
    (fun I ↦ (quotientProfiniteMap O G n rho S tau I).toRingHom)
    (quotientProfiniteMap_compatible O G n rho S tau)

omit [TotallyDisconnectedSpace G] in
lemma profiniteFramedLimitLiftRingHom_continuous :
    Continuous (profiniteFramedLimitLiftRingHom O G n rho S tau) :=
  ProartinianCat.liftCompatibleQuotients_continuous S
    (fun I ↦ (quotientProfiniteMap O G n rho S tau I).toRingHom)
    (quotientProfiniteMap_compatible O G n rho S tau)
    (fun I ↦ (quotientProfiniteMap O G n rho S tau I).cont)

omit [TotallyDisconnectedSpace G] in
lemma profiniteFramedLimitLiftRingHom_commutes (o : O) :
    profiniteFramedLimitLiftRingHom O G n rho S tau
        (algebraMap O (ProfiniteFramedLimit O G n rho) o) = algebraMap O S o := by
  apply ProartinianCat.toOpenIdealLimit_injective S
  apply InverseLimit.ext_lemma
  intro I
  change Ideal.Quotient.mk (ProartinianCat.OpenIdeal.ideal I)
      (profiniteFramedLimitLiftRingHom O G n rho S tau
        (algebraMap O (ProfiniteFramedLimit O G n rho) o)) =
    Ideal.Quotient.mk (ProartinianCat.OpenIdeal.ideal I) (algebraMap O S o)
  have hq := DFunLike.congr_fun (show (Ideal.Quotient.mk
      (ProartinianCat.OpenIdeal.ideal I)).comp
      (profiniteFramedLimitLiftRingHom O G n rho S tau) =
      (quotientProfiniteMap O G n rho S tau I).toRingHom from
    ProartinianCat.quotient_liftCompatibleQuotients S
      (fun I ↦ (quotientProfiniteMap O G n rho S tau I).toRingHom)
      (quotientProfiniteMap_compatible O G n rho S tau) I)
    (algebraMap O (ProfiniteFramedLimit O G n rho) o)
  change Ideal.Quotient.mk (ProartinianCat.OpenIdeal.ideal I)
      (profiniteFramedLimitLiftRingHom O G n rho S tau
        (algebraMap O (ProfiniteFramedLimit O G n rho) o)) =
    quotientProfiniteMap O G n rho S tau I
      (algebraMap O (ProfiniteFramedLimit O G n rho) o) at hq
  rw [hq]
  exact (quotientProfiniteMap O G n rho S tau I).commutes o

/-- A continuous framed lift induces a morphism from the profinite universal ring. -/
noncomputable def profiniteFramedLimitLiftToHom :
    profiniteFramedLimitObject O G n rho ⟶ S where
  hom :=
    { toAlgHom :=
        { toRingHom := profiniteFramedLimitLiftRingHom O G n rho S tau
          commutes' := profiniteFramedLimitLiftRingHom_commutes O G n rho S tau }
      cont := profiniteFramedLimitLiftRingHom_continuous O G n rho S tau }

omit [TotallyDisconnectedSpace G] in
lemma quotientProfiniteMap_universalLift (I : ProartinianCat.OpenIdeal S) :
    (Matrix.GeneralLinearGroup.map
      (quotientProfiniteMap O G n rho S tau I).toRingHom).comp
        (profiniteUniversalLift O G n rho) =
      (quotientContinuousLift O G n (rho := rho) (S := S) tau I).toMonoidHom := by
  ext g i j
  change quotientCompletionMap O G n rho S tau I
      (finiteUniversalLift O G n rho
        (quotientLiftIndex O G n (rho := rho) (tau := tau) S I)
        (QuotientGroup.mk g) i j) =
    Ideal.Quotient.mk (ProartinianCat.OpenIdeal.ideal I) (tau.1 g i j)
  have hmap := DFunLike.congr_fun
    (quotientCompletionMap_universalFramedLift O G n rho S tau I) (QuotientGroup.mk g)
  exact congrArg
    (fun z : GL n (ProartinianCat.openIdealQuotient S I) ↦
      (z : Matrix n n (ProartinianCat.openIdealQuotient S I)) i j) hmap

omit [TotallyDisconnectedSpace G] in
@[simp]
lemma profiniteFramedLimitHomToLift_liftToHom :
    profiniteFramedLimitHomToLift O G n rho S
      (profiniteFramedLimitLiftToHom O G n rho S tau) = tau := by
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro g
  apply Units.ext
  ext i j
  apply ProartinianCat.toOpenIdealLimit_injective S
  apply InverseLimit.ext_lemma
  intro I
  have hquot := DFunLike.congr_fun (ProartinianCat.quotient_liftCompatibleQuotients S
    (fun I ↦ (quotientProfiniteMap O G n rho S tau I).toRingHom)
    (quotientProfiniteMap_compatible O G n rho S tau) I)
    ((profiniteUniversalMatrix O G n rho g) i j)
  have huniv := congrArg
    (fun r : G →* GL n (ProartinianCat.openIdealQuotient S I) ↦ r g i j)
    (quotientProfiniteMap_universalLift O G n rho S tau I)
  change Ideal.Quotient.mk (ProartinianCat.OpenIdeal.ideal I)
      (profiniteFramedLimitLiftRingHom O G n rho S tau
        ((profiniteUniversalMatrix O G n rho g) i j)) =
    Ideal.Quotient.mk (ProartinianCat.OpenIdeal.ideal I) (tau.1 g i j)
  exact hquot.trans huniv
end LiftToHom

omit [TotallyDisconnectedSpace G] in
/-- A morphism out of the profinite framed limit is determined by its universal lift. -/
lemma profiniteFramedLimitHom_unique (S : ProartinianCat O)
    (tau : ContinuousFramedLifts O G n rho S)
    (f : profiniteFramedLimitObject O G n rho ⟶ S)
    (hf : profiniteFramedLimitHomToLift O G n rho S f = tau) :
    f = profiniteFramedLimitLiftToHom O G n rho S tau := by
  have hlifts : profiniteFramedLimitHomToLift O G n rho S f =
      profiniteFramedLimitHomToLift O G n rho S
        (profiniteFramedLimitLiftToHom O G n rho S tau) :=
    hf.trans (profiniteFramedLimitHomToLift_liftToHom O G n rho S tau).symm
  have hA : f.hom.toAlgHom.comp (profiniteFramedRepresentationMap O G n rho) =
      (profiniteFramedLimitLiftToHom O G n rho S tau).hom.toAlgHom.comp
        (profiniteFramedRepresentationMap O G n rho) := by
    apply RingQuot.ringQuot_ext'
    apply MvPolynomial.algHom_ext
    rintro ⟨g, i, j⟩
    have hg := congrArg
      (fun t : ContinuousFramedLifts O G n rho S ↦ t.1 g i j) hlifts
    change f.hom
        (profiniteFramedRepresentationMap O G n rho
          (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j))))) =
      (profiniteFramedLimitLiftToHom O G n rho S tau).hom
        (profiniteFramedRepresentationMap O G n rho
          (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j)))))
    unfold profiniteFramedRepresentationMap
    rw [FramedRepresentationRing.ofRepresentation_generator]
    exact hg
  apply ProartinianCat.hom_ext
  apply DFunLike.ext _ _
  intro x
  apply congr_fun ((profiniteFramedRepresentationMap_denseRange O G n rho).equalizer
    f.hom.cont (profiniteFramedLimitLiftToHom O G n rho S tau).hom.cont ?_) x
  funext a
  exact DFunLike.congr_fun hA a

omit [TotallyDisconnectedSpace G] in
@[simp]
lemma profiniteFramedLimitLiftToHom_homToLift (S : ProartinianCat O)
    (f : profiniteFramedLimitObject O G n rho ⟶ S) :
    profiniteFramedLimitLiftToHom O G n rho S
        (profiniteFramedLimitHomToLift O G n rho S f) = f := by
  symm
  exact profiniteFramedLimitHom_unique O G n rho S
    (profiniteFramedLimitHomToLift O G n rho S f) f rfl

/-- The profinite framed deformation ring corepresents continuous framed lifts of `rho`. -/
noncomputable def profiniteFramedLimitHomEquiv (S : ProartinianCat O) :
    (profiniteFramedLimitObject O G n rho ⟶ S) ≃
      ContinuousFramedLifts O G n rho S where
  toFun := profiniteFramedLimitHomToLift O G n rho S
  invFun := profiniteFramedLimitLiftToHom O G n rho S
  left_inv := profiniteFramedLimitLiftToHom_homToLift O G n rho S
  right_inv := profiniteFramedLimitHomToLift_liftToHom O G n rho S

end

end Deformation

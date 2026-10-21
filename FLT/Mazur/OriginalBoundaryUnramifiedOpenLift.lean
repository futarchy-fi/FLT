/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryNilpotentEndpointLift
public import FLT.Mazur.NilpotentUnramifiedOpenRigidity

/-!
# Full endpoint equations on an unramified image open

The exact scalar-image projection need only be unramified near the second
endpoint. Agreement on the constructed nilpotent comparison test forces the
lifted endpoint into the same open, proving its full equation there.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeFiniteEndpointComparison SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem kernel_le_of_full_lift {X Y Z : Scheme.{0}}
    (a : X ⟶ Y) (b : Z ⟶ Y) (h : ∃ d : Z ⟶ X, d ≫ a = b) :
    RingHom.ker a.appTop.hom ≤ RingHom.ker b.appTop.hom := by
  obtain ⟨d, rfl⟩ := h
  intro r hr
  change (d ≫ a).appTop.hom r = 0
  rw [Scheme.Hom.comp_appTop]
  change d.appTop.hom (a.appTop.hom r) = 0
  rw [show a.appTop.hom r = 0 from hr, map_zero]

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] [Etale p]
  [IsAffine B] [IsNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance openEndpointBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism

include e

/-- Image rigidity forces both full endpoint equations on a nonreduced coefficient scheme. -/
theorem originalBoundary_full_lift_of_unramified_open
    (U : J.subscheme.Opens) [FormallyUnramified (U.ι ≫ projection f)]
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Dense (t ⁻¹' Set.range c))
    (hU : Set.range (t ≫ pullback.snd f f) ⊆ U) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  obtain ⟨d, hd, hi⟩ := originalBoundary_nilpotent_endpoint_equations e J hJ t h
  let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
  have hn := comparison_kernel_sheaf_isNilpotent_of_dense c t h
  have hs : (d ≫ InvariantIdealRelation.snd J p q hJ) ≫ f =
      (t ≫ pullback.snd f f) ≫ f := by
    rw [Category.assoc, ← originalBoundary_scalar_condition p q J hJ,
      ← Category.assoc, hd, Category.assoc, pullback.condition, ← Category.assoc]
  have hy := NilpotentUnramifiedOpenRigidity.hom_ext
    (pullback.snd c t) hn (projection f) U hi
    ((projection_eq_iff f _ _).mpr hs) hU
  have he : d ≫ c = t := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, originalBoundaryComparison, pullback.lift_fst] using hd
    · simpa only [Category.assoc, originalBoundaryComparison, pullback.lift_snd] using hy
  let _ := originalBoundaryComparison_mono e J hJ
  exact ⟨d, he, fun d' hd' ↦ (cancel_mono c).mp (hd'.trans he.symm)⟩

/-- Full comparison equations vanish, including nilpotents, once image rigidity is proved. -/
theorem originalBoundary_full_kernel_of_unramified_open
    (U : J.subscheme.Opens) [FormallyUnramified (U.ι ≫ projection f)]
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Dense (t ⁻¹' Set.range c))
    (hU : Set.range (t ≫ pullback.snd f f) ⊆ U) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom :=
  kernel_le_of_full_lift c t
    (originalBoundary_full_lift_of_unramified_open e J hJ U t h hU).exists

end FLT.Mazur.EquivalenceRelationOrderedFrames

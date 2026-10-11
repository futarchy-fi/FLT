/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothNonspecialDivisorLift
public import FLT.Mazur.SchemeFppfFamilyCover
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A small smooth cover carrying full relative nonspecial divisors

Algebraic closures of the original residue fields give pointed smooth
neighborhoods. Choosing one for each base point produces an actual small fppf
cover. Every member carries a full finite relative Cartier divisor with
acyclic rank-one positive line; no global translation sufficiency is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
open CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme} [IsAffine S] [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (B : X.Modules) (hB : AmpleLineBundle B)

include hB in
/-- Every original base point lies in a smooth chart carrying a full nonspecial divisor. -/
theorem exists_smooth_nonspecial_divisor_over_point (s : S) :
    ∃ (U Z : Scheme) (a : U ⟶ S) (b : Z ⟶ X) (r : Z ⟶ U)
      (D : AcyclicRankOneRelativeDivisor r),
      Smooth a ∧ IsPullback b r f a ∧ s ∈ Set.range a ∧
        IsFinite (D.val.val.subschemeι ≫ r) := by
  let K := AlgebraicClosure (S.residueField s)
  let g : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫ S.fromSpecResidueField s
  let _ : IsIntegral (pullback f g) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd f g)
  let _ : IsAffineHom (pullback.fst f g) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) f g inferInstance
  obtain ⟨U, Z, a, b, r, u, _, D, ha, H, _, hu, _, hD⟩ :=
    exists_smooth_nonspecial_divisor_lift f (IsPullback.of_hasPullback f g) B hB.2.1
      (hB.pullback_affine (pullback.fst f g))
  refine ⟨U, Z, a, b, r, D, ha, H, ?_, hD⟩
  refine ⟨u (IsLocalRing.closedPoint K), ?_⟩
  calc
    a (u (IsLocalRing.closedPoint K)) = (u ≫ a) (IsLocalRing.closedPoint K) := rfl
    _ = g (IsLocalRing.closedPoint K) := congrArg (fun t ↦ t (IsLocalRing.closedPoint K)) hu
    _ = s := S.fromSpecResidueField_apply s _

include hB in
/-- A small smooth fppf cover of the base carries actual full finite nonspecial divisors. -/
theorem exists_smooth_nonspecial_divisor_cover :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage S,
      (∀ i, Smooth (C.f i)) ∧ ∀ i,
        ∃ (Z : Scheme) (b : Z ⟶ X) (r : Z ⟶ C.X i)
          (D : AcyclicRankOneRelativeDivisor r),
          IsPullback b r f (C.f i) ∧ IsFinite (D.val.val.subschemeι ≫ r) := by
  choose U Z a b r D ha H hc hD using exists_smooth_nonspecial_divisor_over_point f B hB
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U a
      (fun s ↦ ⟨s, hc s⟩) (fun s ↦ by
        let _ := ha s
        exact ⟨inferInstance, inferInstance⟩)
  exact ⟨C, ha, fun i ↦ ⟨Z i, b i, r i, D i, H i, hD i⟩⟩

end FLT.Mazur.FCurve

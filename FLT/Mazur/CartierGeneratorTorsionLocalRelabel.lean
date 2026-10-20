/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleGeometricGeneratorRelabel
public import FLT.Mazur.GroupTorsionLocalMatching

/-!
# Cartier generator relabeling through the ambient torsion equation

Unramifiedness of the full ambient torsion equation suffices to match actual
Cartier generators locally. Only their sections are lifted; no annihilation
or etaleness of the whole subgroup is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) [IsSeparated E.group.hom]
  [LocallyOfFiniteType E.group.hom]
  [FormallyUnramified (GroupTorsionScheme.scheme E.group n).hom]
  {P Q : 𝟙_ (Over S) ⟶ H.carrier}

/-- Ambient torsion rigidity gives exact local matches in the original subgroup itself. -/
theorem IsCartierGenerator.exists_local_relabel_of_torsion
    (hP : H.IsCartierGenerator P) (hQ : H.IsCartierGenerator Q) (x : S) :
    ∃ (r : MulAut (Multiplicative (ZMod n))) (U : S.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ ∀ i,
        U.ι ≫ (P ^ (r i).toAdd.val).left = U.ι ≫ (Q ^ i.toAdd.val).left := by
  have hp (i : ℕ) : ((P ^ i) ≫ H.inclusion) ^ n = 1 := by
    rw [← pow_comp, pow_right_comm, hP.1, one_pow, one_comp]
  have hq (i : ℕ) : ((Q ^ i) ≫ H.inclusion) ^ n = 1 := by
    rw [← pow_comp, pow_right_comm, hQ.1, one_pow, one_comp]
  obtain ⟨r, U, hU, hx, he⟩ := GroupTorsionScheme.exists_affine_section_relabel
    E.group n (fun i : Multiplicative (ZMod n) => (P ^ i.toAdd.val) ≫ H.inclusion)
      (fun i : Multiplicative (ZMod n) => (Q ^ i.toAdd.val) ≫ H.inclusion)
      (fun i => hp i.toAdd.val) (fun i => hq i.toAdd.val)
      (fun (r : MulAut (Multiplicative (ZMod n))) i => r i) (by
        intro K _ _ q
        obtain ⟨u, hu⟩ := (hP.baseChange H q).exists_unit_power (H.baseChange q)
          (hQ.baseChange H q)
        refine ⟨CyclicUnitRelabeling.labelAut u, fun i => ?_⟩
        have he : pullSection q P ^ ((CyclicUnitRelabeling.labelAut u) i).toAdd.val =
            pullSection q Q ^ i.toAdd.val := by
          change H.pullGenerator q P ^ _ = H.pullGenerator q Q ^ _
          rw [CyclicUnitRelabeling.relabeled_power _ (hP.baseChange H q).1, hu]
        rw [← section_pow, ← section_pow] at he
        have h := congrArg (fun z => z.left ≫ pullback.fst H.carrier.hom q) he
        simp only [section_fst] at h
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ H.inclusion.left) h).trans (Category.assoc _ _ _))) x
  refine ⟨r, U, hU, hx, fun i => ?_⟩
  apply (cancel_mono H.inclusion.left).mp
  simpa only [Over.comp_left, Category.assoc] using he i

variable {H} {J : F.FiniteSubgroup n}
  [IsSeparated F.group.hom] [LocallyOfFiniteType F.group.hom]
  [FormallyUnramified (GroupTorsionScheme.scheme F.group n).hom]
  (a : CompatibleIso H J) {R : 𝟙_ (Over S) ⟶ J.carrier}

omit [IsSeparated E.group.hom] [LocallyOfFiniteType E.group.hom]
  [FormallyUnramified (GroupTorsionScheme.scheme E.group n).hom] in
/-- The original compatible comparison retains every generator power on one neighborhood. -/
theorem CompatibleIso.exists_local_generator_relabel_of_torsion
    (hP : H.IsCartierGenerator P) (hR : J.IsCartierGenerator R) (x : S) :
    ∃ (r : MulAut (Multiplicative (ZMod n))) (U : S.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ ∀ i,
        U.ι ≫ (P ^ (r i).toAdd.val).left ≫ a.subgroup.hom.left =
          U.ι ≫ (R ^ i.toAdd.val).left := by
  obtain ⟨r, U, hU, hx, he⟩ :=
    (a.cartierGenerator hP).exists_local_relabel_of_torsion J hR x
  refine ⟨r, U, hU, hx, fun i => ?_⟩
  simpa only [← pow_comp, Over.comp_left] using he i

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

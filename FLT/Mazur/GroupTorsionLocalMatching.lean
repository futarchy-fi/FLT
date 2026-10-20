/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupTorsionScheme
public import FLT.Mazur.UnramifiedGeometricSectionMatching

/-!
# Exact local matching inside an unramified torsion equation

Finite families of killed sections lift into the full torsion equalizer.
Geometric relabelings then extend to actual affine neighborhoods, without
requiring an entire finite subgroup to factor through the torsion equation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GroupTorsionScheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom] (n : ℕ)

/-- The full torsion equation inherits local finite type from its ambient group. -/
instance scheme_locallyOfFiniteType [LocallyOfFiniteType E.hom] :
    LocallyOfFiniteType (scheme E n).hom := by
  rw [← Over.w (inclusion E n)]
  infer_instance

variable [FormallyUnramified (scheme E n).hom]
  [LocallyOfFiniteType (scheme E n).hom]

/-- Geometric relabeling of killed sections extends exactly over the original base. -/
theorem exists_affine_section_relabel {L G : Type*} [Finite L]
    (s t : L → (𝟙_ (Over S) ⟶ E))
    (hs : ∀ i, s i ^ n = 1) (ht : ∀ i, t i ^ n = 1) (r : G → L → L)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ S),
      ∃ g, ∀ i, q ≫ (s (r g i)).left = q ≫ (t i).left) (x : S) :
    ∃ (g : G) (U : S.Opens), IsAffineOpen U ∧ x ∈ U ∧
      ∀ i, U.ι ≫ (s (r g i)).left = U.ι ≫ (t i).left := by
  let a i := lift E n (s i) (hs i)
  let b i := lift E n (t i) (ht i)
  have ha i : (a i).left ≫ (inclusion E n).left = (s i).left :=
    congrArg Over.Hom.left (lift_inclusion E n (s i) (hs i))
  have hb i : (b i).left ≫ (inclusion E n).left = (t i).left :=
    congrArg Over.Hom.left (lift_inclusion E n (t i) (ht i))
  obtain ⟨g, U, hU, hx, he⟩ :=
    UnramifiedGeometricSectionMatching.exists_affine_relabel (scheme E n).hom
      (fun i => (a i).left) (fun i => (b i).left)
      (fun _ => Over.w _) (fun _ => Over.w _) r (by
        intro K _ _ q
        obtain ⟨g, hg⟩ := h K q
        refine ⟨g, fun i => ?_⟩
        apply (cancel_mono (inclusion E n).left).mp
        simpa only [Category.assoc, ha, hb] using hg i) x
  refine ⟨g, U, hU, hx, fun i => ?_⟩
  have hi := congrArg (fun z => z ≫ (inclusion E n).left) (he i)
  simpa only [Category.assoc, ha, hb] using hi

end FLT.Mazur.GroupTorsionScheme

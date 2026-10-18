/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicQuotient

/-!
# A single disjoint-union normalized source and its actual relabeling action

The two characteristic choices become components of one scheme. The original
common relabeling group acts by the already constructed component actions.
This union retains the characteristic choice; cross-characteristic moduli
identifications are separate gluing work.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The single scheme assembling both actual normalized characteristic loci. -/
def normalizedDisjointSource : Scheme := ∐ normalizedLocus n

/-- The original normalized locus is an open component of the assembled source. -/
def normalizedDisjointInclusion (b : Bool) :
    normalizedLocus n b ⟶ normalizedDisjointSource n := Sigma.ι (normalizedLocus n) b

/-- Component inclusions are open immersions. -/
instance normalizedDisjointInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (normalizedDisjointInclusion n b) := by
  unfold normalizedDisjointInclusion
  infer_instance

/-- The common original relabeling group acts on the single disjoint-union source. -/
def normalizedDisjointAction : RelabelGroup n →* Aut (normalizedDisjointSource n) where
  toFun g := Sigma.mapIso (fun b => normalizedRelabelAction n b g)
  map_one' := by
    apply Aut.ext
    apply Sigma.hom_ext
    intro b
    simp only [Sigma.ι_mapIso_hom, map_one]
    change 𝟙 _ ≫ Sigma.ι _ b = Sigma.ι _ b ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  map_mul' g h := by
    apply Aut.ext
    apply Sigma.hom_ext
    intro b
    simp only [Aut.Aut_mul_def, Category.assoc, Sigma.ι_mapIso_hom,
      Sigma.ι_mapIso_hom_assoc, map_mul, Iso.trans_hom]

/-- The assembled action retains the exact original action on each characteristic component. -/
@[reassoc] theorem normalizedDisjointAction_inclusion (b : Bool) (g : RelabelGroup n) :
    normalizedDisjointInclusion n b ≫ (normalizedDisjointAction n g).hom =
      (normalizedRelabelAction n b g).hom ≫ normalizedDisjointInclusion n b :=
  Sigma.ι_mapIso_hom _ b

/-- Every point in the single source lies in an original characteristic component. -/
theorem normalizedDisjointSource_covers (x : normalizedDisjointSource n) :
    ∃ b : Bool, x ∈ Set.range (normalizedDisjointInclusion n b) :=
  (sigmaOpenCover (normalizedLocus n)).exists_eq x

/-- The two original characteristic components remain disjoint in this source union. -/
theorem normalizedDisjointInclusion_disjoint (b c : Bool) (h : b ≠ c) :
    Disjoint (normalizedDisjointInclusion n b).opensRange
      (normalizedDisjointInclusion n c).opensRange :=
  disjoint_opensRange_sigmaι _ b c h

end FLT.Mazur.CyclicCharacteristicAtlas

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeStalkExact

/-!
# Insertion on free Cech stalks

A cover member containing the point supplies an extra degeneracy by prepending
its index to each tuple of membership generators.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open AlgebraicTopology FLT.Mazur.CechFreeOpen
open scoped Simplicial

universe u

namespace FLT.Mazur.CechFreeResolution

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The augmented simplicial object of free Cech stalks. -/
def freeStalkAugmented (x : X) : SimplicialObject.Augmented AddCommGrpCat.{u} where
  left := freeSimplicial U ⋙ sheafStalk x
  right := (sheafStalk x).obj integerSheaf
  hom :=
    { app := fun n ↦ (sheafStalk x).map
        (coproductAugmentation ((FormalCoproduct.mk ι U).cech.obj n))
      naturality := fun _ _ f ↦ by
        change (sheafStalk x).map _ ≫ (sheafStalk x).map _ = _ ≫ 𝟙 _
        rw [Category.comp_id, ← Functor.map_comp]
        exact congrArg ((sheafStalk x).map)
          (freeCoproductFunctor_map_augmentation ((FormalCoproduct.mk ι U).cech.map f)) }

/-- Repeating an entry enlarges neither the intersection nor its membership type. -/
def degeneracyInclusion (n : ℕ) (a : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    V U n a ⟶ V U (n + 1) (a ∘ j.predAbove) :=
  homOfLE (le_iInf fun k ↦ iInf_le _ (j.predAbove k))

/-- A degeneracy on a summand repeats the corresponding tuple entry. -/
lemma freeAugmentedι_degeneracy (n : ℕ) (a : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    freeAugmentedι U n a ≫ (freeSimplicial U).σ j =
      freeOpenMap (degeneracyInclusion U n a j) ≫
        freeAugmentedι U (n + 1) (a ∘ j.predAbove) := by
  simp only [freeAugmentedι_eq, Category.assoc]
  simp only [freeSimplicial, SimplicialObject.σ, Functor.comp_map,
    freeCoproductFunctor, FormalCoproduct.eval, FormalCoproduct.cech,
    FormalCoproduct.mapPower, Sigma.ι_comp_desc]
  change freeOpenFunctor.map _ ≫ (freeOpenFunctor.map _ ≫ _) =
    freeOpenFunctor.map _ ≫ (freeOpenFunctor.map _ ≫ _)
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2

/-- A membership generator in a free Cech stalk. -/
def stalkGenerator (n : ℕ) (x : X) (a : Fin (n + 1) → ι)
    (h : OpenFiber (V U n a) x) (z : ℤ) : (freeStalkAugmented U x).left _⦋n⦌ :=
  freeAugmentedStalkι U n x a (Finsupp.single h z)

/-- Membership generators detect morphisms out of every simplicial term. -/
lemma stalkGenerator_hom_ext (n : ℕ) (x : X) {B : AddCommGrpCat.{u}}
    {f g : (freeStalkAugmented U x).left _⦋n⦌ ⟶ B}
    (h : ∀ a p z, f (stalkGenerator U n x a p z) = g (stalkGenerator U n x a p z)) :
    f = g := by
  apply (cancel_epi (freeAugmentedStalkIso U n x).inv).mp
  apply Sigma.hom_ext
  intro a
  have he : Sigma.ι _ a ≫ (freeAugmentedStalkIso U n x).inv =
      freeAugmentedStalkι U n x a := by
    rw [← freeAugmentedStalkι_iso U n x a, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [← Category.assoc, he]
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro p z
  exact h a p z

/-- Faces delete a tuple entry on membership generators. -/
lemma stalkGenerator_face (n : ℕ) (x : X) (a : Fin (n + 2) → ι)
    (h : OpenFiber (V U (n + 1) a) x) (z : ℤ) (j : Fin (n + 2)) :
    (freeStalkAugmented U x).left.δ j (stalkGenerator U (n + 1) x a h z) =
      stalkGenerator U n x (a ∘ j.succAbove)
        (openFiberMap (faceInclusion U n a j) x h) z := by
  have he : freeAugmentedStalkι U (n + 1) x a ≫
      (sheafStalk x).map ((freeSimplicial U).δ j) =
      freeOpenStalkMap (faceInclusion U n a j) x ≫
        freeAugmentedStalkι U n x (a ∘ j.succAbove) := by
    dsimp only [freeAugmentedStalkι]
    rw [Category.assoc, ← Functor.map_comp, freeAugmentedι_face, Functor.map_comp]
    exact freeOpenStalkIso_inv_naturality_assoc (faceInclusion U n a j) x _
  change (freeAugmentedStalkι U (n + 1) x a ≫
    (sheafStalk x).map ((freeSimplicial U).δ j)) (Finsupp.single h z) = _
  rw [he]
  change freeAugmentedStalkι U n x (a ∘ j.succAbove)
    (Finsupp.mapDomain _ (Finsupp.single h z)) = _
  rw [Finsupp.mapDomain_single]
  rfl

/-- Degeneracies repeat a tuple entry on membership generators. -/
lemma stalkGenerator_degeneracy (n : ℕ) (x : X) (a : Fin (n + 1) → ι)
    (h : OpenFiber (V U n a) x) (z : ℤ) (j : Fin (n + 1)) :
    (freeStalkAugmented U x).left.σ j (stalkGenerator U n x a h z) =
      stalkGenerator U (n + 1) x (a ∘ j.predAbove)
        (openFiberMap (degeneracyInclusion U n a j) x h) z := by
  have he : freeAugmentedStalkι U n x a ≫
      (sheafStalk x).map ((freeSimplicial U).σ j) =
      freeOpenStalkMap (degeneracyInclusion U n a j) x ≫
        freeAugmentedStalkι U (n + 1) x (a ∘ j.predAbove) := by
    dsimp only [freeAugmentedStalkι]
    rw [Category.assoc, ← Functor.map_comp, freeAugmentedι_degeneracy, Functor.map_comp]
    exact freeOpenStalkIso_inv_naturality_assoc (degeneracyInclusion U n a j) x _
  change (freeAugmentedStalkι U n x a ≫
    (sheafStalk x).map ((freeSimplicial U).σ j)) (Finsupp.single h z) = _
  rw [he]
  change freeAugmentedStalkι U (n + 1) x (a ∘ j.predAbove)
    (Finsupp.mapDomain _ (Finsupp.single h z)) = _
  rw [Finsupp.mapDomain_single]
  rfl

/-- Membership after prepending a cover member containing the point. -/
def insertionFiber (x : X) (i : ι) (hi : x ∈ U i) (n : ℕ) (a : Fin (n + 1) → ι)
    (h : OpenFiber (V U n a) x) : OpenFiber (V U (n + 1) (Fin.cons i a)) x :=
  ⟨⟨by
    change x ∈ (↑(V U (n + 1) (Fin.cons i a)) : Set X)
    rw [V, Opens.coe_iInf, Set.mem_iInter]
    intro j
    cases j using Fin.cases with
    | zero => exact hi
    | succ j => exact (iInf_le (fun k ↦ U (a k)) j) h.down.down⟩⟩

/-- The insertion morphism extended from membership by free groups and coproducts. -/
def stalkInsertion (x : X) (i : ι) (hi : x ∈ U i) (n : ℕ) :
    (freeStalkAugmented U x).left _⦋n⦌ ⟶ (freeStalkAugmented U x).left _⦋n + 1⦌ :=
  (freeAugmentedStalkIso U n x).hom ≫ Sigma.desc fun a ↦
    AddCommGrpCat.ofHom (Finsupp.mapDomain.addMonoidHom (insertionFiber U x i hi n a)) ≫
      freeAugmentedStalkι U (n + 1) x (Fin.cons i a)

/-- Insertion prepends the chosen index on generators. -/
lemma stalkInsertion_generator (x : X) (i : ι) (hi : x ∈ U i) (n : ℕ)
    (a : Fin (n + 1) → ι) (h : OpenFiber (V U n a) x) (z : ℤ) :
    stalkInsertion U x i hi n (stalkGenerator U n x a h z) =
      stalkGenerator U (n + 1) x (Fin.cons i a) (insertionFiber U x i hi n a h) z := by
  have he : freeAugmentedStalkι U n x a ≫ stalkInsertion U x i hi n =
      AddCommGrpCat.ofHom (Finsupp.mapDomain.addMonoidHom (insertionFiber U x i hi n a)) ≫
        freeAugmentedStalkι U (n + 1) x (Fin.cons i a) := by
    simp [stalkInsertion, freeAugmentedStalkι_iso_assoc]
  change (freeAugmentedStalkι U n x a ≫ stalkInsertion U x i hi n)
    (Finsupp.single h z) = _
  rw [he]
  change freeAugmentedStalkι U (n + 1) x (Fin.cons i a)
    (Finsupp.mapDomain _ (Finsupp.single h z)) = _
  rw [Finsupp.mapDomain_single]
  rfl

/-- Tuple equality suffices for equality of membership generators. -/
lemma stalkGenerator_congr (n : ℕ) (x : X) (a b : Fin (n + 1) → ι)
    (h : OpenFiber (V U n a) x) (k : OpenFiber (V U n b) x) (z : ℤ) (hab : a = b) :
    stalkGenerator U n x a h z = stalkGenerator U n x b k z := by
  subst b
  congr 1
  exact Subsingleton.elim _ _

/-- Deleting the inserted first index recovers the original generator. -/
lemma stalkInsertion_face_zero (x : X) (i : ι) (hi : x ∈ U i) (n : ℕ) :
    stalkInsertion U x i hi n ≫ (freeStalkAugmented U x).left.δ 0 = 𝟙 _ := by
  apply stalkGenerator_hom_ext U n x
  intro a h z
  change (freeStalkAugmented U x).left.δ 0
    (stalkInsertion U x i hi n (stalkGenerator U n x a h z)) = _
  rw [stalkInsertion_generator, stalkGenerator_face]
  apply stalkGenerator_congr
  simp

/-- Insertion commutes with deletion after the first index. -/
lemma stalkInsertion_face_succ (x : X) (i : ι) (hi : x ∈ U i) (n : ℕ)
    (j : Fin (n + 2)) :
    stalkInsertion U x i hi (n + 1) ≫ (freeStalkAugmented U x).left.δ j.succ =
      (freeStalkAugmented U x).left.δ j ≫ stalkInsertion U x i hi n := by
  apply stalkGenerator_hom_ext U (n + 1) x
  intro a h z
  change (freeStalkAugmented U x).left.δ j.succ
    (stalkInsertion U x i hi (n + 1) (stalkGenerator U (n + 1) x a h z)) =
    stalkInsertion U x i hi n
      ((freeStalkAugmented U x).left.δ j (stalkGenerator U (n + 1) x a h z))
  rw [stalkInsertion_generator, stalkGenerator_face, stalkGenerator_face,
    stalkInsertion_generator]
  apply stalkGenerator_congr
  exact Fin.cons_comp_succ_succAbove i a j

/-- Insertion commutes with repetition after the first index. -/
lemma stalkInsertion_degeneracy (x : X) (i : ι) (hi : x ∈ U i) (n : ℕ)
    (j : Fin (n + 1)) :
    stalkInsertion U x i hi n ≫ (freeStalkAugmented U x).left.σ j.succ =
      (freeStalkAugmented U x).left.σ j ≫ stalkInsertion U x i hi (n + 1) := by
  apply stalkGenerator_hom_ext U n x
  intro a h z
  change (freeStalkAugmented U x).left.σ j.succ
    (stalkInsertion U x i hi n (stalkGenerator U n x a h z)) =
    stalkInsertion U x i hi (n + 1)
      ((freeStalkAugmented U x).left.σ j (stalkGenerator U n x a h z))
  rw [stalkInsertion_generator, stalkGenerator_degeneracy, stalkGenerator_degeneracy,
    stalkInsertion_generator]
  apply stalkGenerator_congr
  funext k
  cases k using Fin.cases <;> simp

/-- Augmentation in membership coordinates is independent of the open. -/
lemma stalkOpenAugmentation_single (x : X) (W : Opens X) (h : OpenFiber W x) (z : ℤ) :
    (sheafStalk x).map (freeOpenAugmentation W)
      ((freeOpenStalkIso W x).inv (Finsupp.single h z)) =
    (sheafStalk x).map (freeOpenAugmentation ⊤)
      ((freeOpenStalkIso ⊤ x).inv (Finsupp.single ⟨⟨trivial⟩⟩ z)) := by
  let f : W ⟶ ⊤ := homOfLE le_top
  have he : (freeOpenStalkIso W x).inv ≫
      (sheafStalk x).map (freeOpenAugmentation W) =
      freeOpenStalkMap f x ≫ (freeOpenStalkIso ⊤ x).inv ≫
        (sheafStalk x).map (freeOpenAugmentation ⊤) := by
    rw [← freeOpenMap_augmentation f, Functor.map_comp]
    exact freeOpenStalkIso_inv_naturality_assoc f x _
  change ((freeOpenStalkIso W x).inv ≫
    (sheafStalk x).map (freeOpenAugmentation W)) (Finsupp.single h z) = _
  rw [he]
  change (sheafStalk x).map (freeOpenAugmentation ⊤)
    ((freeOpenStalkIso ⊤ x).inv (Finsupp.mapDomain _ (Finsupp.single h z))) = _
  rw [Finsupp.mapDomain_single]

/-- The augmentation of a degree-zero generator is the same integer generator. -/
lemma stalkGenerator_augmentation (x : X) (a : Fin 1 → ι)
    (h : OpenFiber (V U 0 a) x) (z : ℤ) :
    (freeStalkAugmented U x).hom.app (op ⦋0⦌) (stalkGenerator U 0 x a h z) =
    (sheafStalk x).map (freeOpenAugmentation ⊤)
      ((freeOpenStalkIso ⊤ x).inv (Finsupp.single ⟨⟨trivial⟩⟩ z)) := by
  have he : freeAugmentedStalkι U 0 x a ≫
      (freeStalkAugmented U x).hom.app (op ⦋0⦌) =
      (freeOpenStalkIso (V U 0 a) x).inv ≫
        (sheafStalk x).map (freeOpenAugmentation (V U 0 a)) := by
    change ((freeOpenStalkIso (V U 0 a) x).inv ≫
      (sheafStalk x).map (freeAugmentedι U 0 a)) ≫
        (sheafStalk x).map ((freeAugmented U).d 1 0) = _
    rw [Category.assoc, ← Functor.map_comp]
    congr 1
    apply congrArg ((sheafStalk x).map)
    simpa only [freeAugmentedZeroIso, Iso.refl_hom, Category.comp_id] using
      freeAugmentedι_augmentation U a
  change (freeAugmentedStalkι U 0 x a ≫
    (freeStalkAugmented U x).hom.app (op ⦋0⦌)) (Finsupp.single h z) = _
  rw [he]
  exact stalkOpenAugmentation_single x (V U 0 a) h z

/-- The chosen section returns the singleton tuple on integer generators. -/
lemma stalkSection_generator (x : X) (i : ι) (hi : x ∈ U i)
    (h : OpenFiber (V U 0 (fun _ ↦ i)) x) (z : ℤ) :
    freeAugmentedStalkSection U x i hi
      ((sheafStalk x).map (freeOpenAugmentation ⊤)
        ((freeOpenStalkIso ⊤ x).inv (Finsupp.single ⟨⟨trivial⟩⟩ z))) =
      stalkGenerator U 0 x (fun _ ↦ i) h z := by
  rw [← stalkOpenAugmentation_single x (V U 0 (fun _ ↦ i)) h z]
  have := freeOpenAugmentation_stalk_isIso (V U 0 (fun _ ↦ i)) x h.down.down
  have he : (sheafStalk x).map (freeOpenAugmentation (V U 0 (fun _ ↦ i))) ≫
      freeAugmentedStalkSection U x i hi =
      (sheafStalk x).map (freeAugmentedι U 0 (fun _ ↦ i)) := by
    simp [freeAugmentedStalkSection, freeAugmentedZeroIso]
  change ((sheafStalk x).map (freeOpenAugmentation (V U 0 (fun _ ↦ i))) ≫
    freeAugmentedStalkSection U x i hi)
      ((freeOpenStalkIso (V U 0 (fun _ ↦ i)) x).inv (Finsupp.single h z)) = _
  rw [he]
  rfl

/-- Deleting the old vertex after insertion factors through the augmentation. -/
lemma stalkInsertion_face_one (x : X) (i : ι) (hi : x ∈ U i) :
    stalkInsertion U x i hi 0 ≫ (freeStalkAugmented U x).left.δ 1 =
      (freeStalkAugmented U x).hom.app (op ⦋0⦌) ≫
        freeAugmentedStalkSection U x i hi := by
  apply stalkGenerator_hom_ext U 0 x
  intro a h z
  change (freeStalkAugmented U x).left.δ 1
    (stalkInsertion U x i hi 0 (stalkGenerator U 0 x a h z)) =
    freeAugmentedStalkSection U x i hi
      ((freeStalkAugmented U x).hom.app (op ⦋0⦌) (stalkGenerator U 0 x a h z))
  rw [stalkInsertion_generator, stalkGenerator_face, stalkGenerator_augmentation,
    stalkSection_generator U x i hi ⟨⟨by simpa [V] using hi⟩⟩]
  apply stalkGenerator_congr
  ext j
  fin_cases j
  rfl

/-- A containing cover member supplies all five extra-degeneracy identities. -/
def freeStalkExtraDegeneracy (x : X) (i : ι) (hi : x ∈ U i) :
    (freeStalkAugmented U x).ExtraDegeneracy where
  s' := freeAugmentedStalkSection U x i hi
  s := stalkInsertion U x i hi
  s'_comp_ε := freeAugmentedStalkSection_d U x i hi
  s₀_comp_δ₁ := stalkInsertion_face_one U x i hi
  s_comp_δ₀ := stalkInsertion_face_zero U x i hi
  s_comp_δ := stalkInsertion_face_succ U x i hi
  s_comp_σ := stalkInsertion_degeneracy U x i hi

end FLT.Mazur.CechFreeResolution

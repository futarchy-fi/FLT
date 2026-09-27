/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerComultiplication

/-!
# Hopf structure on the Kummer coordinate algebra

The carry formula defines an associative multiplication with identity and inverses.
We verify these identities on component coordinates.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace KummerAlgebra

variable (R : Type*) [CommRing R] (n : ℕ) (u : Rˣ) (hn : 0 < n)
variable {S : Type*} [CommRing S] [Algebra R S]

/-- A root in component `i` defines a point, without any domain assumption on the target. -/
noncomputable def rootPoint (i : Fin n) (x : S)
    (hx : x ^ n = algebraMap R S ((u : R) ^ i.val)) : Coordinate R n u →ₐ[R] S :=
  (componentPoint R n u i x hx).comp (Pi.evalAlgHom R (Component R n u) i)

/-- Convolution using the explicit Kummer comultiplication. -/
noncomputable def convolution (f g : Coordinate R n u →ₐ[R] S) :
    Coordinate R n u →ₐ[R] S :=
  (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)).comp (comul R n u hn)

/-- A pair of component maps evaluates a tensor through its corresponding component. -/
theorem lift_component (i j : Fin n) (f : Component R n u i →ₐ[R] S)
    (g : Component R n u j →ₐ[R] S) (a : Coordinate R n u ⊗[R] Coordinate R n u) :
    Algebra.TensorProduct.lift
        (f.comp (Pi.evalAlgHom R (Component R n u) i))
        (g.comp (Pi.evalAlgHom R (Component R n u) j)) (fun _ _ ↦ .all _ _) a =
      Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)
        (tensorComponentsEquiv R n u a i j) := by
  induction a using TensorProduct.inductionOn with
  | tmul a b => simp
  | add a b ha hb => simp_all

/-- Convolution of component points is the Kummer carry formula. -/
theorem convolution_rootPoint (i j : Fin n) (x y : S)
    (hx : x ^ n = algebraMap R S ((u : R) ^ i.val))
    (hy : y ^ n = algebraMap R S ((u : R) ^ j.val)) :
    convolution R n u hn (rootPoint R n u i x hx) (rootPoint R n u j y hy) =
      rootPoint R n u (sumComponent n hn i j)
        (x * y * algebraMap R S ((↑u⁻¹ : R) ^ ((i.val + j.val) / n)))
        (mul_carry_pow R n u hx hy (Nat.mod_add_div _ _).symm) := by
  have h : (Algebra.TensorProduct.lift (componentPoint R n u i x hx)
      (componentPoint R n u j y hy) (fun _ _ ↦ .all _ _)).comp
      (componentComul R n u hn i j) =
      componentPoint R n u (sumComponent n hn i j)
        (x * y * algebraMap R S ((↑u⁻¹ : R) ^ ((i.val + j.val) / n)))
        (mul_carry_pow R n u hx hy (Nat.mod_add_div _ _).symm) := by
    apply AdjoinRoot.algHom_ext
    simp [multiplicationRoot, -AdjoinRoot.algebraMap_eq, mul_comm, mul_left_comm, mul_assoc]
  ext a
  change Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (comul R n u hn a) = _
  dsimp only [rootPoint]
  rw [lift_component, comul_component]
  exact AlgHom.congr_fun h _

/-- Equality of an index and a root determines equality of the corresponding points. -/
theorem rootPoint_congr {i j : Fin n} {x y : S}
    {hx : x ^ n = algebraMap R S ((u : R) ^ i.val)}
    {hy : y ^ n = algebraMap R S ((u : R) ^ j.val)}
    (hij : i = j) (hxy : x = y) : rootPoint R n u i x hx = rootPoint R n u j y hy := by
  subst j
  subst y
  rfl

/-- Component zero with root one is a left identity for convolution. -/
theorem convolution_zero_left (i : Fin n) (x : S)
    (hx : x ^ n = algebraMap R S ((u : R) ^ i.val)) :
    convolution R n u hn (rootPoint R n u ⟨0, hn⟩ 1 (by simp))
      (rootPoint R n u i x hx) = rootPoint R n u i x hx := by
  rw [convolution_rootPoint]
  apply rootPoint_congr
  · apply Fin.ext
    simp [sumComponent, Nat.mod_eq_of_lt i.isLt]
  · simp [Nat.div_eq_of_lt i.isLt]

/-- Component zero with root one is a right identity for convolution. -/
theorem convolution_zero_right (i : Fin n) (x : S)
    (hx : x ^ n = algebraMap R S ((u : R) ^ i.val)) :
    convolution R n u hn (rootPoint R n u i x hx)
      (rootPoint R n u ⟨0, hn⟩ 1 (by simp)) = rootPoint R n u i x hx := by
  rw [convolution_rootPoint]
  apply rootPoint_congr
  · apply Fin.ext
    simp [sumComponent, Nat.mod_eq_of_lt i.isLt]
  · simp [Nat.div_eq_of_lt i.isLt]

/-- Changing the target algebra commutes with convolution. -/
theorem comp_convolution {T : Type*} [CommRing T] [Algebra R T]
    (h : S →ₐ[R] T) (f g : Coordinate R n u →ₐ[R] S) :
    h.comp (convolution R n u hn f g) =
      convolution R n u hn (h.comp f) (h.comp g) := by
  have hh : h.comp (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)) =
      Algebra.TensorProduct.lift (h.comp f) (h.comp g) (fun _ _ ↦ .all _ _) := by
    ext <;> simp
  simp only [convolution, ← AlgHom.comp_assoc, hh]

/-- The universal point in one component is its coordinate projection. -/
theorem rootPoint_root (i : Fin n) :
    rootPoint R n u i (AdjoinRoot.root (equation R n u i)) (root_pow R n u i) =
      Pi.evalAlgHom R (Component R n u) i := by
  have h : componentPoint R n u i (AdjoinRoot.root (equation R n u i))
      (root_pow R n u i) = AlgHom.id R _ := by
    apply AdjoinRoot.algHom_ext
    simp
  simp [rootPoint, h]

/-- A scalar extension of the counit is the point with index zero and root one. -/
theorem ofId_comp_counit :
    (Algebra.ofId R S).comp (counit R n u hn) =
      rootPoint R n u ⟨0, hn⟩ (1 : S) (by simp) := by
  have h : (Algebra.ofId R S).comp (componentPoint R n u ⟨0, hn⟩ (1 : R) (by simp)) =
      componentPoint R n u ⟨0, hn⟩ (1 : S) (by simp) := by
    apply AdjoinRoot.algHom_ext
    simp
  simpa only [counit, rootPoint, ← AlgHom.comp_assoc] using
    congrArg (fun f ↦ f.comp (Pi.evalAlgHom R (Component R n u) ⟨0, hn⟩)) h

/-- The carry exponents obey the cocycle identity for three component indices. -/
theorem carry_assoc (hn : 0 < n) (i j k : Fin n) :
    (i.val + j.val) / n + (((i.val + j.val) % n + k.val) / n) =
      (j.val + k.val) / n + ((i.val + (j.val + k.val) % n) / n) := by
  apply Nat.eq_of_mul_eq_mul_left hn
  have h₁ := Nat.mod_add_div (i.val + j.val) n
  have h₂ := Nat.mod_add_div (j.val + k.val) n
  have h₃ := Nat.mod_add_div ((i.val + j.val) % n + k.val) n
  have h₄ := Nat.mod_add_div (i.val + (j.val + k.val) % n) n
  have hm : ((i.val + j.val) % n + k.val) % n =
      (i.val + (j.val + k.val) % n) % n := by
    simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]
  simp only [Nat.mul_add]
  omega

/-- Convolution is associative on component points over any commutative algebra. -/
theorem convolution_rootPoint_assoc (i j k : Fin n) (x y z : S)
    (hx : x ^ n = algebraMap R S ((u : R) ^ i.val))
    (hy : y ^ n = algebraMap R S ((u : R) ^ j.val))
    (hz : z ^ n = algebraMap R S ((u : R) ^ k.val)) :
    convolution R n u hn
      (convolution R n u hn (rootPoint R n u i x hx) (rootPoint R n u j y hy))
      (rootPoint R n u k z hz) =
    convolution R n u hn (rootPoint R n u i x hx)
      (convolution R n u hn (rootPoint R n u j y hy) (rootPoint R n u k z hz)) := by
  simp only [convolution_rootPoint]
  apply rootPoint_congr
  · apply Fin.ext
    simp only [sumComponent, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]
  · dsimp only [sumComponent]
    simp only [map_pow]
    calc
      x * y * (algebraMap R S) ↑u⁻¹ ^ ((↑i + ↑j) / n) * z *
          (algebraMap R S) ↑u⁻¹ ^ (((↑i + ↑j) % n + ↑k) / n) =
        x * y * z * (algebraMap R S) ↑u⁻¹ ^
          ((↑i + ↑j) / n + ((↑i + ↑j) % n + ↑k) / n) := by
            rw [pow_add]
            ring
      _ = _ := by
        rw [carry_assoc n hn i j k, pow_add]
        ring

/-- Convolution with the counit on the left fixes the universal point. -/
theorem convolution_counit_left :
    convolution R n u hn ((Algebra.ofId R (Coordinate R n u)).comp (counit R n u hn))
      (AlgHom.id R _) = AlgHom.id R _ := by
  apply AlgHom.ext
  intro a
  funext i
  let e := Pi.evalAlgHom R (Component R n u) i
  change (e.comp (convolution R n u hn _ _)) a = e a
  rw [comp_convolution]
  have h : e.comp ((Algebra.ofId R (Coordinate R n u)).comp (counit R n u hn)) =
      (Algebra.ofId R (Component R n u i)).comp (counit R n u hn) := by
    ext b
    rfl
  rw [h, AlgHom.comp_id, ofId_comp_counit]
  change convolution R n u hn _ (Pi.evalAlgHom R (Component R n u) i) a = _
  rw [← rootPoint_root, convolution_zero_left, rootPoint_root]

/-- Convolution with the counit on the right fixes the universal point. -/
theorem convolution_counit_right :
    convolution R n u hn (AlgHom.id R _)
      ((Algebra.ofId R (Coordinate R n u)).comp (counit R n u hn)) = AlgHom.id R _ := by
  apply AlgHom.ext
  intro a
  funext i
  let e := Pi.evalAlgHom R (Component R n u) i
  change (e.comp (convolution R n u hn _ _)) a = e a
  rw [comp_convolution]
  have h : e.comp ((Algebra.ofId R (Coordinate R n u)).comp (counit R n u hn)) =
      (Algebra.ofId R (Component R n u i)).comp (counit R n u hn) := by
    ext b
    rfl
  rw [h, AlgHom.comp_id, ofId_comp_counit]
  change convolution R n u hn (Pi.evalAlgHom R (Component R n u) i) _ a = _
  rw [← rootPoint_root, convolution_zero_right, rootPoint_root]

/-- The Kummer comultiplication satisfies the left counit identity. -/
theorem counit_comul :
    (Algebra.TensorProduct.map (counit R n u hn) (AlgHom.id R (Coordinate R n u))).comp
      (comul R n u hn) = (Algebra.TensorProduct.lid R (Coordinate R n u)).symm.toAlgHom := by
  have h : (Algebra.TensorProduct.lid R (Coordinate R n u)).toAlgHom.comp
      (Algebra.TensorProduct.map (counit R n u hn) (AlgHom.id R (Coordinate R n u))) =
      Algebra.TensorProduct.lift
        ((Algebra.ofId R (Coordinate R n u)).comp (counit R n u hn))
        (AlgHom.id R _) (fun _ _ ↦ .all _ _) := by
    ext <;> simp [Algebra.smul_def]
  apply AlgHom.ext
  intro a
  apply (Algebra.TensorProduct.lid R (Coordinate R n u)).injective
  change ((Algebra.TensorProduct.lid R (Coordinate R n u)).toAlgHom.comp
    (Algebra.TensorProduct.map (counit R n u hn) (AlgHom.id R _)))
      (comul R n u hn a) = _
  rw [h]
  simpa [convolution]
    using AlgHom.congr_fun (convolution_counit_left R n u hn) a

/-- The Kummer comultiplication satisfies the right counit identity. -/
theorem comul_counit :
    (Algebra.TensorProduct.map (AlgHom.id R (Coordinate R n u)) (counit R n u hn)).comp
      (comul R n u hn) = (Algebra.TensorProduct.rid R R (Coordinate R n u)).symm.toAlgHom := by
  have h : (Algebra.TensorProduct.rid R R (Coordinate R n u)).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R (Coordinate R n u)) (counit R n u hn)) =
      Algebra.TensorProduct.lift (AlgHom.id R _)
        ((Algebra.ofId R (Coordinate R n u)).comp (counit R n u hn))
        (fun _ _ ↦ .all _ _) := by
    ext <;> simp [Algebra.smul_def]
  apply AlgHom.ext
  intro a
  apply (Algebra.TensorProduct.rid R R (Coordinate R n u)).injective
  change ((Algebra.TensorProduct.rid R R (Coordinate R n u)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R _) (counit R n u hn)))
      (comul R n u hn a) = _
  rw [h]
  simpa [convolution]
    using AlgHom.congr_fun (convolution_counit_right R n u hn) a

/-- Tensor cubes separate into triples of Kummer components. -/
noncomputable def tripleComponentsEquiv :
    Coordinate R n u ⊗[R] (Coordinate R n u ⊗[R] Coordinate R n u) ≃ₐ[R]
      ((j k i : Fin n) → Component R n u i ⊗[R]
        (Component R n u j ⊗[R] Component R n u k)) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : Coordinate R n u ≃ₐ[R] _)
    (tensorComponentsEquiv R n u)).trans <|
  (Algebra.TensorProduct.piRight R R (Coordinate R n u)
    (fun j ↦ (k : Fin n) → Component R n u j ⊗[R] Component R n u k)).trans <|
  AlgEquiv.piCongrRight fun j ↦
    (Algebra.TensorProduct.piRight R R (Coordinate R n u)
      (fun k ↦ Component R n u j ⊗[R] Component R n u k)).trans <|
    AlgEquiv.piCongrRight fun k ↦
      (Algebra.TensorProduct.comm R (Coordinate R n u) _).trans <|
      (Algebra.TensorProduct.piRight R R
        (Component R n u j ⊗[R] Component R n u k) (Component R n u)).trans <|
      AlgEquiv.piCongrRight fun _i ↦ Algebra.TensorProduct.comm R _ _

/-- The tensor-cube decomposition preserves the three factors. -/
@[simp] theorem tripleComponentsEquiv_tmul
    (a b c : Coordinate R n u) (i j k : Fin n) :
    tripleComponentsEquiv R n u (a ⊗ₜ[R] (b ⊗ₜ[R] c)) j k i =
      a i ⊗ₜ[R] (b j ⊗ₜ[R] c k) := by
  simp [tripleComponentsEquiv]

/-- Postcomposition sends a root point to the point with the mapped root. -/
theorem comp_rootPoint {T : Type*} [CommRing T] [Algebra R T]
    (h : S →ₐ[R] T) (i : Fin n) (x : S)
    (hx : x ^ n = algebraMap R S ((u : R) ^ i.val)) :
    h.comp (rootPoint R n u i x hx) =
      rootPoint R n u i (h x) (by rw [← map_pow, hx, h.commutes]) := by
  have he : h.comp (componentPoint R n u i x hx) =
      componentPoint R n u i (h x) (by rw [← map_pow, hx, h.commutes]) := by
    apply AdjoinRoot.algHom_ext
    simp
  simpa only [rootPoint, ← AlgHom.comp_assoc] using
    congrArg (fun f ↦ f.comp (Pi.evalAlgHom R (Component R n u) i)) he

/-- Evaluation of the left iterated comultiplication is left-associated convolution. -/
theorem lift_iterated_comul_left (f g h : Coordinate R n u →ₐ[R] S)
    (a : Coordinate R n u) :
    Algebra.TensorProduct.lift f (Algebra.TensorProduct.lift g h (fun _ _ ↦ .all _ _))
      (fun _ _ ↦ .all _ _)
      ((Algebra.TensorProduct.assoc R R R (Coordinate R n u) _ _)
        (Algebra.TensorProduct.map (comul R n u hn) (AlgHom.id R _) (comul R n u hn a))) =
    convolution R n u hn (convolution R n u hn f g) h a := by
  have h₁ : (Algebra.TensorProduct.lift f
      (Algebra.TensorProduct.lift g h (fun _ _ ↦ .all _ _)) (fun _ _ ↦ .all _ _)).comp
      (Algebra.TensorProduct.assoc R R R (Coordinate R n u) _ _).toAlgHom =
      Algebra.TensorProduct.lift (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _))
        h (fun _ _ ↦ .all _ _) := by
    ext <;> simp [Algebra.TensorProduct.one_def]
  have h₂ : (Algebra.TensorProduct.lift
      (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)) h (fun _ _ ↦ .all _ _)).comp
      (Algebra.TensorProduct.map (comul R n u hn) (AlgHom.id R _)) =
      Algebra.TensorProduct.lift (convolution R n u hn f g) h (fun _ _ ↦ .all _ _) := by
    ext <;> simp [convolution]
  exact (AlgHom.congr_fun h₁ _).trans (AlgHom.congr_fun h₂ (comul R n u hn a))

/-- Evaluation of the right iterated comultiplication is right-associated convolution. -/
theorem lift_iterated_comul_right (f g h : Coordinate R n u →ₐ[R] S)
    (a : Coordinate R n u) :
    Algebra.TensorProduct.lift f (Algebra.TensorProduct.lift g h (fun _ _ ↦ .all _ _))
      (fun _ _ ↦ .all _ _)
      (Algebra.TensorProduct.map (AlgHom.id R _) (comul R n u hn) (comul R n u hn a)) =
    convolution R n u hn f (convolution R n u hn g h) a := by
  have he : (Algebra.TensorProduct.lift f
      (Algebra.TensorProduct.lift g h (fun _ _ ↦ .all _ _)) (fun _ _ ↦ .all _ _)).comp
      (Algebra.TensorProduct.map (AlgHom.id R _) (comul R n u hn)) =
      Algebra.TensorProduct.lift f (convolution R n u hn g h) (fun _ _ ↦ .all _ _) := by
    ext <;> simp [convolution]
  exact AlgHom.congr_fun he (comul R n u hn a)

/-- Projection of a tensor cube is evaluation at the three universal component points. -/
theorem tripleComponentsEquiv_apply (i j k : Fin n)
    (a : Coordinate R n u ⊗[R] (Coordinate R n u ⊗[R] Coordinate R n u)) :
    let S := Component R n u i ⊗[R] (Component R n u j ⊗[R] Component R n u k)
    let f : Coordinate R n u →ₐ[R] S :=
      Algebra.TensorProduct.includeLeft.comp (Pi.evalAlgHom R (Component R n u) i)
    let g : Coordinate R n u →ₐ[R] S :=
      Algebra.TensorProduct.includeRight.comp
        (Algebra.TensorProduct.includeLeft.comp (Pi.evalAlgHom R (Component R n u) j))
    let h : Coordinate R n u →ₐ[R] S :=
      Algebra.TensorProduct.includeRight.comp
        (Algebra.TensorProduct.includeRight.comp (Pi.evalAlgHom R (Component R n u) k))
    tripleComponentsEquiv R n u a j k i =
      Algebra.TensorProduct.lift f (Algebra.TensorProduct.lift g h (fun _ _ ↦ .all _ _))
        (fun _ _ ↦ .all _ _) a := by
  dsimp only
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp_all
  | tmul a b =>
    induction b using TensorProduct.inductionOn with
    | add b c hb hc => simp_all [TensorProduct.tmul_add]
    | tmul b c => simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- The Kummer comultiplication is coassociative. -/
theorem coassoc :
    (Algebra.TensorProduct.assoc R R R (Coordinate R n u) _ _).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul R n u hn) (AlgHom.id R _)).comp (comul R n u hn)) =
    (Algebra.TensorProduct.map (AlgHom.id R _) (comul R n u hn)).comp (comul R n u hn) := by
  apply AlgHom.ext
  intro a
  apply (tripleComponentsEquiv R n u).injective
  funext j k i
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, tripleComponentsEquiv_apply]
  rw [lift_iterated_comul_left, lift_iterated_comul_right]
  let S := Component R n u i ⊗[R] (Component R n u j ⊗[R] Component R n u k)
  let fi : Component R n u i →ₐ[R] S := Algebra.TensorProduct.includeLeft
  let fj : Component R n u j →ₐ[R] S :=
    Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft
  let fk : Component R n u k →ₐ[R] S :=
    Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight
  change convolution R n u hn
      (convolution R n u hn (fi.comp (Pi.evalAlgHom R (Component R n u) i))
        (fj.comp (Pi.evalAlgHom R (Component R n u) j)))
      (fk.comp (Pi.evalAlgHom R (Component R n u) k)) a =
    convolution R n u hn (fi.comp (Pi.evalAlgHom R (Component R n u) i))
      (convolution R n u hn (fj.comp (Pi.evalAlgHom R (Component R n u) j))
        (fk.comp (Pi.evalAlgHom R (Component R n u) k))) a
  rw [← rootPoint_root R n u i, ← rootPoint_root R n u j, ← rootPoint_root R n u k]
  simp only [comp_rootPoint]
  rw [convolution_rootPoint_assoc]

/-- The Kummer coordinate algebra carries the bialgebra defined by the carry formula. -/
@[instance_reducible]
noncomputable def bialgebra : Bialgebra R (Coordinate R n u) :=
  Bialgebra.ofAlgHom (comul R n u hn) (counit R n u hn)
    (coassoc R n u hn) (counit_comul R n u hn) (comul_counit R n u hn)

end KummerAlgebra

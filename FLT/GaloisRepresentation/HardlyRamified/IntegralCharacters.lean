/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Slop.Ribet_Lemma.LatticeTameTwo
public import FLT.Slop.Ribet_Lemma.LatticeFlat
public import FLT.Slop.Ribet_Lemma.Brauer_Nesbitt

/-!
# Integral characters of reducible representations

The integral submodule associated to a generic line is its intersection with
the ambient lattice. A primitive functional identifies the quotient with the
coefficient ring and proves that this intersection is saturated. Both
characters are continuous and inherit finite-flat models at every open
coefficient ideal. Their product is the cyclotomic character under HR.

The unconditional endpoint proves unramifiedness away from two and three.
The full C0 conclusion is proved conditionally on square-zero inertia at two;
deriving that arithmetic input from the HR quotient at two remains open.
-/

@[expose] public section

open Module
open scoped TensorProduct NumberField

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan

section Intersection

variable {O K W : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]

/-- The intersection of an integral lattice with a generic subspace, viewed
as a submodule of the lattice. -/
def latticeIntersection (Λ : Submodule O W) (L : Submodule K W) : Submodule O Λ :=
  (L.restrictScalars O).comap Λ.subtype

/-- Intersections with generic subspaces are saturated. -/
theorem latticeIntersection_saturated (Λ : Submodule O W) (L : Submodule K W)
    (a : O) (ha : a ≠ 0) (x : Λ)
    (hx : a • x ∈ latticeIntersection Λ L) : x ∈ latticeIntersection Λ L := by
  have haK : algebraMap O K a ≠ 0 :=
    fun h ↦ ha (IsFractionRing.injective O K (by simpa using h))
  change (x : W) ∈ L
  change a • (x : W) ∈ L at hx
  have h : algebraMap O K a • (x : W) ∈ L := by
    simpa only [algebraMap_smul] using hx
  simpa only [inv_smul_smul₀ haK] using L.smul_mem (algebraMap O K a)⁻¹ h

/-- A codimension-one generic subspace is the kernel of a nonzero functional. -/
theorem exists_functional_ker_eq [FiniteDimensional K W]
    (L : Submodule K W) (hL : Module.finrank K (W ⧸ L) = 1) :
    ∃ f : W →ₗ[K] K, f ≠ 0 ∧ LinearMap.ker f = L := by
  let e : (W ⧸ L) ≃ₗ[K] K := LinearEquiv.ofFinrankEq _ _ (by simpa using hL)
  let f := e.toLinearMap.comp L.mkQ
  have hf : Function.Surjective f := e.surjective.comp L.mkQ_surjective
  refine ⟨f, ?_, ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := hf 1
    simp [h] at hx
  · ext x
    change e (L.mkQ x) = 0 ↔ x ∈ L
    rw [e.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- The saturated intersection with a generic line is the kernel of an
integral surjection. No choice of a basis of the ambient lattice is required. -/
theorem exists_primitive_quotient_of_line (Λ : Submodule O W)
    [Submodule.IsLattice K Λ] (hdim : Module.finrank K W = 2)
    (L : Submodule K W) (hL : Module.finrank K L = 1) :
    ∃ π : Λ →ₗ[O] O, Function.Surjective π ∧
      LinearMap.ker π = latticeIntersection Λ L := by
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨f, hf, hker⟩ := exists_functional_ker_eq L (by
    rw [Submodule.finrank_quotient, hdim, hL])
  obtain ⟨π, a, ha, hπ, hfa⟩ := exists_primitive_lattice_functional Λ f hf
  refine ⟨π, hπ, ?_⟩
  ext x
  change π x = 0 ↔ (x : W) ∈ L
  rw [← hker, LinearMap.mem_ker, hfa, mul_eq_zero]
  simp only [ha, or_false, map_eq_zero_iff _ (IsFractionRing.injective O K)]

/-- Both terms of the integral filtration are free of rank one. The quotient
is identified with `O` by the primitive functional. -/
theorem latticeIntersection_rank_one (Λ : Submodule O W)
    [Submodule.IsLattice K Λ] (hdim : Module.finrank K W = 2)
    (L : Submodule K W) (hL : Module.finrank K L = 1) :
    Module.Free O (latticeIntersection Λ L) ∧
      Module.finrank O (latticeIntersection Λ L) = 1 ∧
      Nonempty ((Λ ⧸ latticeIntersection Λ L) ≃ₗ[O] O) := by
  obtain ⟨π, hπ, hker⟩ := exists_primitive_quotient_of_line Λ hdim L hL
  have he : Nonempty ((Λ ⧸ latticeIntersection Λ L) ≃ₗ[O] O) := by
    rw [← hker]
    exact ⟨π.quotKerEquivOfSurjective hπ⟩
  obtain ⟨e⟩ := he
  refine ⟨inferInstance, ?_, ⟨e⟩⟩
  have hr := (latticeIntersection Λ L).finrank_quotient_add_finrank
  rw [e.finrank_eq, Module.finrank_self,
    Submodule.IsLattice.finrank_eq (K := K) Λ, hdim] at hr
  omega

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/-- A stable generic subspace gives a stable saturated integral submodule. -/
theorem latticeIntersection_stable {G : Type*} [Group G]
    (ρ : Representation K G W) (Λ : Submodule O W)
    (hΛ : StableLattice.Stabilizes ρ Λ) (L : Submodule K W)
    (hL : ∀ g, L.map (ρ g) ≤ L) (g : G) :
    (latticeIntersection Λ L).map (StableLattice.latticeRep ρ Λ hΛ g) ≤
      latticeIntersection Λ L := by
  rintro _ ⟨x, hx, rfl⟩
  exact hL g (Submodule.mem_map_of_mem hx)

end Intersection

section CharacterPredicates

variable {G O : Type*} [Group G] [CommRing O]

/-- A type synonym carrying the scalar action of a character. -/
@[nolint unusedArguments]
def CharacterSpace (_ψ : G →* Oˣ) := O

/-- Forget the character action on a scalar. -/
def CharacterSpace.val {ψ : G →* Oˣ} (x : CharacterSpace ψ) : O := x

instance (ψ : G →* Oˣ) : AddCommGroup (CharacterSpace ψ) :=
  inferInstanceAs (AddCommGroup O)

instance (ψ : G →* Oˣ) : DistribMulAction G (CharacterSpace ψ) where
  smul g x := @Mul.mul O _ (ψ g : O) x
  one_smul x := by
    change @Mul.mul O _ (ψ 1 : O) x = x
    simp only [map_one, Units.val_one]
    exact @one_mul O _ x
  mul_smul g h x := by
    change @Mul.mul O _ (ψ (g * h) : O) x =
      @Mul.mul O _ (ψ g : O) (@Mul.mul O _ (ψ h : O) x)
    simp only [map_mul, Units.val_mul]
    exact @mul_assoc O _ _ _ x
  smul_zero g := @mul_zero O _ (ψ g : O)
  smul_add g x y := @mul_add O _ _ _ (ψ g : O) x y

variable [TopologicalSpace O]

/-- Every open-ideal reduction of the rank-one character has a finite-flat
model at three. This does not use the rank-two hardly-ramified predicate. -/
def Flat3 (ψ : Field.absoluteGaloisGroup ℚ →* Oˣ) : Prop :=
  let v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (by decide : Nat.Prime 3)
  ∀ I : Ideal O, IsOpen (I : Set O) →
    GaloisModule.IsFiniteFlat (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      (AlgebraicClosure (v.adicCompletion ℚ))
      (CharacterSpace (((Units.map (Ideal.Quotient.mk I).toMonoidHom).comp ψ).comp
        (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))).toMonoidHom))

omit [TopologicalSpace O] in
/-- All finite inertia groups away from three act trivially on the character. -/
def UnramifiedOutsideThree (ψ : Field.absoluteGaloisGroup ℚ →* Oˣ) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), p ≠ 3 →
    let v := hp.toHeightOneSpectrumRingOfIntegersRat
    localInertiaGroup v ≤ (ψ.comp
      (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))).toMonoidHom).ker

end CharacterPredicates

section IntegralExtension

variable {O K W : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]

/-- A generic extension of two integral characters, together with its actual
integral lattice, injection and quotient map. The integral exact sequence is
`0 → O → Λ → O → 0`, with the specified character actions. -/
def GenericExtensionOf (ρ : Representation K (Field.absoluteGaloisGroup ℚ) W)
    (ψ₁ ψ₂ : Field.absoluteGaloisGroup ℚ →* Oˣ) : Prop :=
  StableLattice.IsExtensionOf ρ
    ((Units.map (algebraMap O K).toMonoidHom).comp ψ₁)
    ((Units.map (algebraMap O K).toMonoidHom).comp ψ₂) ∧
  ∃ (Λ : Submodule O W) (hΛ : StableLattice.IsStableLattice ρ Λ)
    (i : O →ₗ[O] Λ) (π : Λ →ₗ[O] O),
    Function.Injective i ∧ Function.Surjective π ∧ LinearMap.range i = LinearMap.ker π ∧
    (∀ g a, StableLattice.latticeRep ρ Λ hΛ.stable g (i a) = i ((ψ₁ g : O) * a)) ∧
    (∀ g x, π (StableLattice.latticeRep ρ Λ hΛ.stable g x) = (ψ₂ g : O) * π x)

end IntegralExtension

section ContinuousCharacters

variable {O M : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [AddCommGroup M] [Module O M]

/-- Scalar multiplication by a continuous character is a continuous rank-one
Galois representation for the module topology. -/
def characterGaloisRep (ψ : Field.absoluteGaloisGroup ℚ →* Oˣ) (hc : Continuous ψ) :
    GaloisRep ℚ O O :=
  letI := moduleTopology O (Module.End O O)
  letI : ContinuousAdd (Module.End O O) := ModuleTopology.continuousAdd O _
  { toMonoidHom := (Algebra.lsmul O O O).toMonoidHom.comp ((Units.coeHom O).comp ψ)
    continuous_toFun := (IsModuleTopology.continuous_of_linearMap
      (Algebra.lsmul O O O : O →ₐ[O] Module.End O O).toLinearMap).comp
        (Units.continuous_val.comp hc) }

/-- A scalar character is continuous if its value can be recovered by an
integral linear functional on the orbit of one vector. -/
theorem continuous_character_of_evaluation (ρ : GaloisRep ℚ O M)
    (ψ : Field.absoluteGaloisGroup ℚ →* Oˣ) (p : M →ₗ[O] O) (v : M)
    (hv : ∀ g, p (ρ g v) = (ψ g : O)) : Continuous ψ := by
  let := moduleTopology O (Module.End O M)
  let f : Module.End O M →ₗ[O] O := p.comp (LinearMap.applyₗ v)
  have h : Continuous (fun g ↦ (ψ g : O)) := by
    have he : (fun g ↦ (ψ g : O)) = fun g ↦ f (ρ g) := funext fun g ↦ (hv g).symm
    rw [he]
    exact (IsModuleTopology.continuous_of_linearMap f).comp ρ.continuous
  apply Units.continuous_iff.mpr
  refine ⟨h, ?_⟩
  convert h.comp continuous_inv using 1
  ext g
  simp

/-- A stable direct summand of rank one carries a continuous integral
character. The retraction only splits the underlying module. -/
theorem exists_continuous_character_of_split_line (ρ : GaloisRep ℚ O M)
    (i : O →ₗ[O] M) (p : M →ₗ[O] O) (hpi : ∀ a, p (i a) = a)
    (hstab : ∀ g, (LinearMap.range i).map (ρ g) ≤ LinearMap.range i) :
    ∃ ψ : Field.absoluteGaloisGroup ℚ →* Oˣ, Continuous ψ ∧
      ∀ g a, ρ g (i a) = i ((ψ g : O) * a) := by
  let c (g : Field.absoluteGaloisGroup ℚ) : O := p (ρ g (i 1))
  have hact (g : Field.absoluteGaloisGroup ℚ) (a : O) :
      ρ g (i a) = i (c g * a) := by
    obtain ⟨b, hb⟩ := hstab g (Submodule.mem_map_of_mem (LinearMap.mem_range_self i 1))
    have hcb : c g = b := by
      change p (ρ g (i 1)) = b
      rw [← hb, hpi]
    calc
      ρ g (i a) = a • ρ g (i 1) := by rw [← map_smul, ← map_smul]; simp
      _ = i (c g * a) := by rw [← hb, ← map_smul, hcb]; simp [mul_comm]
  let χ : Field.absoluteGaloisGroup ℚ →* O :=
    { toFun := c
      map_one' := by simp [c, hpi]
      map_mul' := by
        intro g h
        change p (ρ (g * h) (i 1)) = c g * c h
        rw [map_mul, Module.End.mul_apply, hact, mul_one, hact, hpi] }
  refine ⟨χ.toHomUnits, ?_, ?_⟩
  · exact continuous_character_of_evaluation ρ χ.toHomUnits p (i 1) (fun _ ↦ rfl)
  · exact hact

/-- A rank-one quotient with stable kernel carries a continuous integral
character. Surjectivity supplies an integral vector at which to evaluate it. -/
theorem exists_continuous_character_of_quotient (ρ : GaloisRep ℚ O M)
    (π : M →ₗ[O] O) (hπ : Function.Surjective π)
    (hstab : ∀ g, (LinearMap.ker π).map (ρ g) ≤ LinearMap.ker π) :
    ∃ ψ : Field.absoluteGaloisGroup ℚ →* Oˣ, Continuous ψ ∧
      ∀ g x, π (ρ g x) = (ψ g : O) * π x := by
  obtain ⟨v, hv⟩ := hπ 1
  let c (g : Field.absoluteGaloisGroup ℚ) : O := π (ρ g v)
  have hact (g : Field.absoluteGaloisGroup ℚ) (x : M) :
      π (ρ g x) = c g * π x := by
    have hx : x - π x • v ∈ LinearMap.ker π := by
      simp [LinearMap.mem_ker, hv]
    have h := hstab g (Submodule.mem_map_of_mem hx)
    have he : π (ρ g x) - π x * c g = 0 := by
      simpa [LinearMap.mem_ker, c] using h
    simpa [mul_comm] using sub_eq_zero.mp he
  let χ : Field.absoluteGaloisGroup ℚ →* O :=
    { toFun := c
      map_one' := by simpa [c] using hv
      map_mul' := by
        intro g h
        change π (ρ (g * h) v) = c g * c h
        rw [map_mul, Module.End.mul_apply, hact] }
  refine ⟨χ.toHomUnits, ?_, ?_⟩
  · exact continuous_character_of_evaluation ρ χ.toHomUnits π v (fun _ ↦ rfl)
  · exact hact

end ContinuousCharacters

section Assembly

variable {O K W : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]

omit [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O K]
  [IsFractionRing O K] [Module O W] [IsScalarTower O K W] in
/-- Reducibility in dimension two supplies a stable generic line. -/
theorem exists_stable_line_of_reducible {G : Type*} [Group G]
    (ρ : Representation K G W) (hdim : Module.finrank K W = 2)
    (hred : ¬ ρ.IsIrreducible) :
    ∃ L : Submodule K W, Module.finrank K L = 1 ∧ ∀ g, L.map (ρ g) ≤ L := by
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial W := Module.finrank_pos_iff.mp
    (show 0 < Module.finrank K W by omega)
  have : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have he : (⊥ : Submodule K W) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top he
  have hex : ∃ L : Subrepresentation ρ, L ≠ ⊥ ∧ L ≠ ⊤ := by
    by_contra! h
    exact hred ⟨fun L ↦ or_iff_not_imp_left.mpr (h L)⟩
  obtain ⟨L, hbot, htop⟩ := hex
  have hb : L.toSubmodule ≠ ⊥ := fun h ↦ hbot (Subrepresentation.toSubmodule_injective h)
  have ht : L.toSubmodule ≠ ⊤ := fun h ↦ htop (Subrepresentation.toSubmodule_injective h)
  refine ⟨L.toSubmodule, ?_, fun g ↦ ?_⟩
  · have hp : 0 < Module.finrank K L.toSubmodule :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hb)
    have hlt : Module.finrank K L.toSubmodule < Module.finrank K W :=
      Submodule.finrank_lt ht
    omega
  · rintro _ ⟨x, hx, rfl⟩
    exact L.apply_mem_toSubmodule g hx

/-- A primitive quotient whose kernel has rank one has an integral kernel
generator and a linear retraction onto that generator. -/
theorem exists_split_kernel_generator {M : Type*} [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Free O M]
    (π : M →ₗ[O] O) (hπ : Function.Surjective π)
    (hdim : Module.finrank O (LinearMap.ker π) = 1) :
    ∃ (i : O →ₗ[O] M) (p : M →ₗ[O] O),
      (∀ a, p (i a) = a) ∧ LinearMap.range i = LinearMap.ker π := by
  obtain ⟨v, hv⟩ := hπ 1
  let e : (LinearMap.ker π) ≃ₗ[O] O := LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  let r : M →ₗ[O] LinearMap.ker π :=
    (LinearMap.id - (LinearMap.toSpanSingleton O M v).comp π).codRestrict
      (LinearMap.ker π) (fun x ↦ by simp [LinearMap.mem_ker, hv])
  let i : O →ₗ[O] M := (LinearMap.ker π).subtype.comp e.symm.toLinearMap
  let p : M →ₗ[O] O := e.toLinearMap.comp r
  have hr (x : LinearMap.ker π) : r x = x := by
    apply Subtype.ext
    change (x : M) - π x • v = x
    rw [x.property, zero_smul, sub_zero]
  refine ⟨i, p, ?_, ?_⟩
  · intro a
    change e (r (e.symm a)) = a
    rw [hr, e.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e.symm a).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩

variable [TopologicalSpace O] [IsTopologicalRing O]
  [TopologicalSpace K] [IsTopologicalRing K]

/-- A stable generic line gives continuous integral sub- and quotient
characters, with explicit maps and the saturated kernel. -/
theorem integral_characters_of_stable_line (ρK : GaloisRep ℚ K W)
    (Λ : Submodule O W) (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (hdim : Module.finrank K W = 2)
    (L : Submodule K W) (hL : Module.finrank K L = 1)
    (hstab : ∀ g, L.map (ρK.toRepresentation g) ≤ L) :
    ∃ (ψ₁ ψ₂ : Field.absoluteGaloisGroup ℚ →* Oˣ)
      (i : O →ₗ[O] Λ) (π p : Λ →ₗ[O] O),
      Continuous ψ₁ ∧ Continuous ψ₂ ∧ Function.Injective i ∧ Function.Surjective π ∧
      LinearMap.range i = latticeIntersection Λ L ∧
      LinearMap.ker π = latticeIntersection Λ L ∧
      (∀ a, p (i a) = a) ∧
      (∀ g a, latticeGaloisRep ρK Λ hΛ hOK g (i a) = i ((ψ₁ g : O) * a)) ∧
      (∀ g x, π (latticeGaloisRep ρK Λ hΛ hOK g x) = (ψ₂ g : O) * π x) := by
  let := hΛ.isLattice
  obtain ⟨π, hπ, hker⟩ := exists_primitive_quotient_of_line Λ hdim L hL
  have hrank : Module.finrank O (LinearMap.ker π) = 1 := by
    rw [hker]
    exact (latticeIntersection_rank_one Λ hdim L hL).2.1
  obtain ⟨i, p, hpi, hi⟩ := exists_split_kernel_generator π hπ hrank
  have hstable (g : Field.absoluteGaloisGroup ℚ) :
      (LinearMap.ker π).map (latticeGaloisRep ρK Λ hΛ hOK g) ≤ LinearMap.ker π := by
    rw [hker]
    exact latticeIntersection_stable ρK.toRepresentation Λ hΛ.stable L hstab g
  obtain ⟨ψ₁, hc₁, h₁⟩ := exists_continuous_character_of_split_line
    (latticeGaloisRep ρK Λ hΛ hOK) i p hpi (by simpa only [hi] using hstable)
  obtain ⟨ψ₂, hc₂, h₂⟩ := exists_continuous_character_of_quotient
    (latticeGaloisRep ρK Λ hΛ hOK) π hπ hstable
  exact ⟨ψ₁, ψ₂, i, π, p, hc₁, hc₂, Function.LeftInverse.injective hpi, hπ,
    hi.trans hker, hker, hpi, h₁, h₂⟩

/-- The integral filtration recovers the extension of generic characters. -/
theorem genericExtensionOf_of_integral_maps (ρK : GaloisRep ℚ K W)
    (Λ : Submodule O W) (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K))
    (L : Submodule K W) (hL : Module.finrank K L = 1)
    (ψ₁ ψ₂ : Field.absoluteGaloisGroup ℚ →* Oˣ)
    (i : O →ₗ[O] Λ) (π : Λ →ₗ[O] O)
    (hi : Function.Injective i) (hπ : Function.Surjective π)
    (hrange : LinearMap.range i = latticeIntersection Λ L)
    (hker : LinearMap.ker π = latticeIntersection Λ L)
    (h₁ : ∀ g a, latticeGaloisRep ρK Λ hΛ hOK g (i a) = i ((ψ₁ g : O) * a))
    (h₂ : ∀ g x, π (latticeGaloisRep ρK Λ hΛ hOK g x) = (ψ₂ g : O) * π x) :
    GenericExtensionOf ρK.toRepresentation ψ₁ ψ₂ := by
  let := hΛ.isLattice
  refine ⟨⟨L, hL, ?_, ?_⟩,
    ⟨Λ, hΛ, i, π, hi, hπ, hrange.trans hker.symm, h₁, h₂⟩⟩
  · intro g x hx
    change ρK g x = algebraMap O K (ψ₁ g : O) • x
    obtain ⟨a, ha, hax⟩ := Submodule.IsLattice.exists_smul_mem Λ x
    have haK : algebraMap O K a ≠ 0 :=
      fun h ↦ ha (IsFractionRing.injective O K (by simpa using h))
    have hm : (⟨a • x, hax⟩ : Λ) ∈ LinearMap.range i := by
      rw [hrange]
      exact (L.restrictScalars O).smul_mem a hx
    obtain ⟨b, hb⟩ := hm
    have he : ρK g (a • x) = (ψ₁ g : O) • (a • x) := by
      have hh := congrArg Subtype.val (h₁ g b)
      change ρK g (i b : W) = (i ((ψ₁ g : O) * b) : W) at hh
      rw [show (ψ₁ g : O) * b = (ψ₁ g : O) • b from rfl, map_smul] at hh
      change ρK g (i b : W) = (ψ₁ g : O) • (i b : W) at hh
      simpa only [hb] using hh
    have he' : algebraMap O K a • ρK g x =
        algebraMap O K a • (algebraMap O K (ψ₁ g : O) • x) := by
      simpa only [← algebraMap_smul K a, map_smul, ← algebraMap_smul K (ψ₁ g : O),
        smul_comm (algebraMap O K a)] using he
    have hh := congrArg (fun y : W ↦ (algebraMap O K a)⁻¹ • y) he'
    simpa only [inv_smul_smul₀ haK] using hh
  · intro g x
    change ρK g x - algebraMap O K (ψ₂ g : O) • x ∈ L
    obtain ⟨a, ha, hax⟩ := Submodule.IsLattice.exists_smul_mem Λ x
    have haK : algebraMap O K a ≠ 0 :=
      fun h ↦ ha (IsFractionRing.injective O K (by simpa using h))
    let y : Λ := ⟨a • x, hax⟩
    have hm : latticeGaloisRep ρK Λ hΛ hOK g y - (ψ₂ g : O) • y ∈ LinearMap.ker π := by
      simp [LinearMap.mem_ker, h₂]
    rw [hker] at hm
    have he : algebraMap O K a • (ρK g x - algebraMap O K (ψ₂ g : O) • x) ∈ L := by
      change ρK g (a • x) - (ψ₂ g : O) • (a • x) ∈ L at hm
      simpa only [← algebraMap_smul K a, map_smul, ← algebraMap_smul K (ψ₂ g : O),
        smul_comm (algebraMap O K a), smul_sub] using hm
    simpa only [inv_smul_smul₀ haK] using L.smul_mem (algebraMap O K a)⁻¹ he

/-- The algebraic and continuity part of C0, before its arithmetic conditions:
a reducible generic fibre has an integral extension by continuous characters. -/
theorem integral_characters_of_reducible_algebraic (ρK : GaloisRep ℚ K W)
    (Λ : Submodule O W) (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (hdim : Module.finrank K W = 2)
    (hred : ¬ ρK.IsIrreducible) :
    ∃ ψ₁ ψ₂ : Field.absoluteGaloisGroup ℚ →* Oˣ,
      Continuous ψ₁ ∧ Continuous ψ₂ ∧ GenericExtensionOf ρK.toRepresentation ψ₁ ψ₂ := by
  obtain ⟨L, hL, hstab⟩ := exists_stable_line_of_reducible ρK.toRepresentation hdim hred
  obtain ⟨ψ₁, ψ₂, i, π, p, hc₁, hc₂, hi, hπ, hrange, hker, _, h₁, h₂⟩ :=
    integral_characters_of_stable_line ρK Λ hΛ hOK hdim L hL hstab
  exact ⟨ψ₁, ψ₂, hc₁, hc₂, genericExtensionOf_of_integral_maps
    ρK Λ hΛ hOK L hL ψ₁ ψ₂ i π hi hπ hrange hker h₁ h₂⟩

end Assembly

section FlatCharacters

variable {O M : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [IsLocalRing O] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]

/-- Finite flatness at three descends to an integral rank-one quotient at
every open coefficient ideal. -/
theorem flat3_of_quotient (ρ : GaloisRep ℚ O M)
    (hflat : ρ.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (by decide : Nat.Prime 3)))
    (ψ : Field.absoluteGaloisGroup ℚ →* Oˣ)
    (π : M →ₗ[O] O) (hπ : Function.Surjective π)
    (heq : ∀ g x, π (ρ g x) = (ψ g : O) * π x) : Flat3 ψ := by
  intro I hI
  let v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (by decide : Nat.Prime 3)
  let σ := (ρ.baseChange (O ⧸ I)).toLocal v
  let χ : Field.absoluteGaloisGroup (v.adicCompletion ℚ) →* (O ⧸ I)ˣ :=
    ((Units.map (Ideal.Quotient.mk I).toMonoidHom).comp ψ).comp
      (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))).toMonoidHom
  let q₀ : (O ⧸ I) ⊗[O] M →ₗ[O] (O ⧸ I) :=
    (TensorProduct.rid O (O ⧸ I)).toLinearMap.comp (π.lTensor (O ⧸ I))
  have hq₀ (r : O ⧸ I) (x : M) : q₀ (r ⊗ₜ[O] x) = π x • r := by
    simp [q₀]
  let q : σ.Space →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] CharacterSpace χ :=
    { toFun := q₀
      map_zero' := q₀.map_zero
      map_add' := q₀.map_add
      map_smul' := by
        intro g x
        change q₀ (σ g x) = (χ g : O ⧸ I) * q₀ x
        induction x using TensorProduct.inductionOn with
        | tmul r x =>
          change q₀ (r ⊗ₜ[O] ρ _ x) = _
          rw [hq₀, hq₀, heq]
          simp only [χ, MonoidHom.comp_apply, Units.coe_map,
            RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Algebra.smul_def, map_mul, mul_assoc]
          congr 8
          exact Subsingleton.elim _ _
        | add x y hx hy => simp [map_add, hx, hy, mul_add] }
  apply (hflat.cond I hI).quotient _ _ _ _ q
  intro r
  obtain ⟨x, hx⟩ := hπ 1
  refine ⟨(r : O ⧸ I) ⊗ₜ[O] x, ?_⟩
  change q₀ ((r : O ⧸ I) ⊗ₜ[O] x) = r
  rw [hq₀, hx, one_smul]

/-- An integral split injection remains injective at every coefficient
quotient, so finite-flat subobjects give flatness of the subcharacter. -/
theorem flat3_of_split_subcharacter (ρ : GaloisRep ℚ O M)
    (hflat : ρ.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (by decide : Nat.Prime 3)))
    (ψ : Field.absoluteGaloisGroup ℚ →* Oˣ)
    (i : O →ₗ[O] M) (p : M →ₗ[O] O) (hpi : ∀ a, p (i a) = a)
    (heq : ∀ g a, ρ g (i a) = i ((ψ g : O) * a)) : Flat3 ψ := by
  intro I hI
  let v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (by decide : Nat.Prime 3)
  let σ := (ρ.baseChange (O ⧸ I)).toLocal v
  let χ : Field.absoluteGaloisGroup (v.adicCompletion ℚ) →* (O ⧸ I)ˣ :=
    ((Units.map (Ideal.Quotient.mk I).toMonoidHom).comp ψ).comp
      (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))).toMonoidHom
  let j : CharacterSpace χ →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] σ.Space :=
    { toFun := fun r ↦ CharacterSpace.val r ⊗ₜ[O] i 1
      map_zero' := by
        change (0 : O ⧸ I) ⊗ₜ[O] i 1 = 0
        exact TensorProduct.zero_tmul _ _
      map_add' := fun x y ↦
        TensorProduct.add_tmul (CharacterSpace.val x) (CharacterSpace.val y) (i 1)
      map_smul' := by
        intro g r
        change ((χ g : O ⧸ I) * CharacterSpace.val r) ⊗ₜ[O] i 1 =
          CharacterSpace.val r ⊗ₜ[O] ρ _ (i 1)
        rw [heq, mul_one]
        have hi (a : O) : i a = a • i 1 := by rw [← map_smul]; simp
        conv_rhs => rw [hi]
        simp only [χ, MonoidHom.comp_apply, Units.coe_map]
        change ((algebraMap O (O ⧸ I)) _ * CharacterSpace.val r) ⊗ₜ[O] i 1 = _
        rw [← Algebra.smul_def, TensorProduct.smul_tmul]
        congr 1
        congr 1
        congr 5
        exact Subsingleton.elim _ _ }
  apply (hflat.cond I hI).subobject _ _ _ _ j
  intro r s hrs
  let q₀ : (O ⧸ I) ⊗[O] M →ₗ[O] (O ⧸ I) :=
    (TensorProduct.rid O (O ⧸ I)).toLinearMap.comp (p.lTensor (O ⧸ I))
  have h := congrArg q₀ hrs
  change q₀ (CharacterSpace.val r ⊗ₜ[O] i 1) =
    q₀ (CharacterSpace.val s ⊗ₜ[O] i 1) at h
  change CharacterSpace.val r = CharacterSpace.val s
  simpa [q₀, hpi] using h

end FlatCharacters

section Determinant

variable {O M G : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] [Group G]

/-- The determinant of an integral extension is the product of its two
characters; the proof uses the actual free kernel and quotient. -/
theorem determinant_of_integral_extension (ρ : Representation O G M)
    (hdim : Module.finrank O M = 2) (ψ₁ ψ₂ : G →* Oˣ)
    (i : O →ₗ[O] M) (π : M →ₗ[O] O) (hπ : Function.Surjective π)
    (hexact : LinearMap.range i = LinearMap.ker π)
    (h₁ : ∀ g a, ρ g (i a) = i ((ψ₁ g : O) * a))
    (h₂ : ∀ g x, π (ρ g x) = (ψ₂ g : O) * π x) (g : G) :
    LinearMap.det (ρ g) = (ψ₁ g : O) * (ψ₂ g : O) := by
  let e := π.quotKerEquivOfSurjective hπ
  let : Module.Free O (M ⧸ LinearMap.ker π) := Module.Free.of_equiv e.symm
  have hq : Module.finrank O (M ⧸ LinearMap.ker π) = 1 := by
    rw [e.finrank_eq, Module.finrank_self]
  have hk : Module.finrank O (LinearMap.ker π) = 1 := by
    have h := (LinearMap.ker π).finrank_quotient_add_finrank
    rw [hq, hdim] at h
    omega
  have hstable : LinearMap.ker π ≤ (LinearMap.ker π).comap (ρ g) := by
    intro x hx
    change π (ρ g x) = 0
    rw [h₂, hx, mul_zero]
  have hres : (ρ g).restrict hstable =
      (ψ₁ g : O) • (LinearMap.id : LinearMap.ker π →ₗ[O] LinearMap.ker π) := by
    ext x
    have hx : (x : M) ∈ LinearMap.range i := by rw [hexact]; exact x.property
    obtain ⟨a, ha⟩ := hx
    change ρ g x = (ψ₁ g : O) • (x : M)
    rw [← ha, h₁]
    exact i.map_smul (ψ₁ g : O) a
  have hquot : (LinearMap.ker π).mapQ (LinearMap.ker π) (ρ g) hstable =
      (ψ₂ g : O) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (Submodule.Quotient.mk (ρ g x) : M ⧸ LinearMap.ker π) =
        Submodule.Quotient.mk ((ψ₂ g : O) • x)
      rw [Submodule.Quotient.eq]
      simp [LinearMap.mem_ker, h₂]
  rw [(ρ g).det_eq_det_mul_det (LinearMap.ker π) hstable, hres, hquot,
    LinearMap.det_smul, LinearMap.det_smul, hk, hq, pow_one, pow_one,
    LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

omit [IsDomain O] [IsPrincipalIdealRing O] [Module.Free O M] [Module.Finite O M] in
/-- An element acting trivially on the lattice acts trivially on both
rank-one characters of an integral exact sequence. -/
theorem characters_eq_one_of_action_eq_one (ρ : Representation O G M)
    (ψ₁ ψ₂ : G →* Oˣ) (i : O →ₗ[O] M) (π : M →ₗ[O] O)
    (hi : Function.Injective i) (hπ : Function.Surjective π)
    (h₁ : ∀ g a, ρ g (i a) = i ((ψ₁ g : O) * a))
    (h₂ : ∀ g x, π (ρ g x) = (ψ₂ g : O) * π x)
    (g : G) (hg : ρ g = 1) : ψ₁ g = 1 ∧ ψ₂ g = 1 := by
  constructor
  · apply Units.ext
    apply hi
    simpa [hg] using (h₁ g 1).symm
  · apply Units.ext
    obtain ⟨x, hx⟩ := hπ 1
    simpa [hg, hx] using (h₂ g x).symm

omit [IsPrincipalIdealRing O] [Module.Free O M] [Module.Finite O M] in
/-- Square-zero unipotence forces both rank-one characters to be trivial
over a domain. This uses reducedness, not a characteristic-three cube identity. -/
theorem characters_eq_one_of_sub_one_sq_eq_zero (ρ : Representation O G M)
    (ψ₁ ψ₂ : G →* Oˣ) (i : O →ₗ[O] M) (π : M →ₗ[O] O)
    (hi : Function.Injective i) (hπ : Function.Surjective π)
    (h₁ : ∀ g a, ρ g (i a) = i ((ψ₁ g : O) * a))
    (h₂ : ∀ g x, π (ρ g x) = (ψ₂ g : O) * π x)
    (g : G) (hg : (ρ g - 1) ^ 2 = 0) : ψ₁ g = 1 ∧ ψ₂ g = 1 := by
  let N := ρ g - 1
  have hsub (a : O) : N (i a) = i (((ψ₁ g : O) - 1) * a) := by
    change ρ g (i a) - i a = _
    rw [h₁, sub_mul, one_mul, map_sub]
  have hquot (x : M) : π (N x) = ((ψ₂ g : O) - 1) * π x := by
    change π (ρ g x - x) = _
    rw [map_sub, h₂, sub_mul, one_mul]
  have hN (x : M) : N (N x) = 0 := by
    change ((ρ g - 1) * (ρ g - 1)) x = 0
    rw [← pow_two, hg, LinearMap.zero_apply]
  constructor
  · apply Units.ext
    apply sub_eq_zero.mp
    apply (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp
    apply hi
    simpa only [hsub, mul_one, ← pow_two, map_zero, Units.val_one] using hN (i 1)
  · apply Units.ext
    apply sub_eq_zero.mp
    apply (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp
    obtain ⟨x, hx⟩ := hπ 1
    have hh := congrArg π (hN x)
    simpa only [hquot, hx, mul_one, ← pow_two, map_zero, Units.val_one] using hh

end Determinant

section HardlyRamified

variable {O K W : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
  [TopologicalSpace O] [IsTopologicalRing O]
  [TopologicalSpace K] [IsTopologicalRing K] [Algebra ℤ_[3] O]

/-- The coefficient image of the three-adic cyclotomic character. -/
def threeAdicCyclotomic : Field.absoluteGaloisGroup ℚ →* Oˣ :=
  (Units.map (algebraMap ℤ_[3] O).toMonoidHom).comp
    ((cyclotomicCharacter (AlgebraicClosure ℚ) 3).comp
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ) (AlgebraicClosure ℚ)))

/-- C0 with the inertia-at-two conclusion left out: the characters are
continuous, flat at every open level, unramified away from two and three,
and their product is the cyclotomic character. The HR input is supplied
directly on the lattice, independently of lattice HR transport. -/
theorem integral_characters_of_reducible_away_two (ρK : GaloisRep ℚ K W)
    (Λ : Submodule O W) (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (hdim : Module.rank K W = 2)
    (hρΛ : letI := hΛ.isLattice
      GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide)
        ((Submodule.IsLattice.rank' K Λ).trans hdim) (latticeGaloisRep ρK Λ hΛ hOK))
    (hred : ¬ ρK.IsIrreducible) :
    ∃ ψ₁ ψ₂ : Field.absoluteGaloisGroup ℚ →* Oˣ,
      Continuous ψ₁ ∧ Continuous ψ₂ ∧ Flat3 ψ₁ ∧ Flat3 ψ₂ ∧
      GenericExtensionOf ρK.toRepresentation ψ₁ ψ₂ ∧
      ψ₁ * ψ₂ = threeAdicCyclotomic ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 2 ∧ p ≠ 3 →
        let v := hp.toHeightOneSpectrumRingOfIntegersRat
        ∀ g ∈ localInertiaGroup v,
          ψ₁ (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) g) = 1 ∧
          ψ₂ (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) g) = 1) ∧
      ∀ g, (latticeGaloisRep ρK Λ hΛ hOK g - 1) ^ 2 = 0 → ψ₁ g = 1 ∧ ψ₂ g = 1 := by
  let := hΛ.isLattice
  have hdimK : Module.finrank K W = 2 := Module.finrank_eq_of_rank_eq hdim
  have hdimO : Module.finrank O Λ = 2 := by
    rw [Submodule.IsLattice.finrank_eq (K := K) Λ, hdimK]
  obtain ⟨L, hL, hstab⟩ := exists_stable_line_of_reducible ρK.toRepresentation hdimK hred
  obtain ⟨ψ₁, ψ₂, i, π, r, hc₁, hc₂, hi, hπ, hrange, hker, hri, h₁, h₂⟩ :=
    integral_characters_of_stable_line ρK Λ hΛ hOK hdimK L hL hstab
  let ρ := latticeGaloisRep ρK Λ hΛ hOK
  refine ⟨ψ₁, ψ₂, hc₁, hc₂,
    flat3_of_split_subcharacter ρ hρΛ.isFlat ψ₁ i r hri h₁,
    flat3_of_quotient ρ hρΛ.isFlat ψ₂ π hπ h₂,
    genericExtensionOf_of_integral_maps ρK Λ hΛ hOK L hL ψ₁ ψ₂ i π hi hπ hrange hker h₁ h₂,
    ?_, ?_, ?_⟩
  · apply MonoidHom.ext
    intro g
    apply Units.ext
    change (ψ₁ g : O) * (ψ₂ g : O) =
      algebraMap ℤ_[3] O (cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv)
    rw [← determinant_of_integral_extension ρ.toRepresentation hdimO ψ₁ ψ₂ i π hπ
      (hrange.trans hker.symm) h₁ h₂ g]
    exact hρΛ.det g
  · intro p hp hgood
    dsimp only
    intro g hg
    have hur := hρΛ.isUnramified p hp hgood
    have hgρ := hur.localInertiaGroup_le hg
    apply characters_eq_one_of_action_eq_one ρ.toRepresentation ψ₁ ψ₂ i π hi hπ h₁ h₂
    change ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat g = 1 at hgρ
    change ρ (Field.absoluteGaloisGroup.map _ g) = 1 at hgρ
    change ρ (Field.absoluteGaloisGroup.map _ g) = 1
    convert hgρ using 1
    congr 3
    exact Subsingleton.elim _ _
  · exact characters_eq_one_of_sub_one_sq_eq_zero ρ.toRepresentation ψ₁ ψ₂ i π hi hπ h₁ h₂

/-- The full C0 conclusion conditional on the remaining arithmetic input:
inertia at two acts with square-zero difference from the identity on the
given lattice. This condition is not assumed to follow from HR here. -/
theorem integral_characters_of_reducible_of_inertia_two (ρK : GaloisRep ℚ K W)
    (Λ : Submodule O W) (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (hdim : Module.rank K W = 2)
    (hρΛ : letI := hΛ.isLattice
      GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide)
        ((Submodule.IsLattice.rank' K Λ).trans hdim) (latticeGaloisRep ρK Λ hΛ hOK))
    (hred : ¬ ρK.IsIrreducible)
    (hI₂ : let v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (by decide : Nat.Prime 2)
      ∀ g ∈ localInertiaGroup v,
        (latticeGaloisRep ρK Λ hΛ hOK
          (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) g) - 1) ^ 2 = 0) :
    ∃ ψ₁ ψ₂ : Field.absoluteGaloisGroup ℚ →* Oˣ,
      Continuous ψ₁ ∧ Continuous ψ₂ ∧ Flat3 ψ₁ ∧ Flat3 ψ₂ ∧
      UnramifiedOutsideThree ψ₁ ∧ UnramifiedOutsideThree ψ₂ ∧
      GenericExtensionOf ρK.toRepresentation ψ₁ ψ₂ ∧ ψ₁ * ψ₂ = threeAdicCyclotomic := by
  obtain ⟨ψ₁, ψ₂, hc₁, hc₂, hf₁, hf₂, hext, hdet, hur, hsq⟩ :=
    integral_characters_of_reducible_away_two ρK Λ hΛ hOK hdim hρΛ hred
  have hu (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
      let v := hp.toHeightOneSpectrumRingOfIntegersRat
      ∀ g ∈ localInertiaGroup v,
        ψ₁ (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) g) = 1 ∧
        ψ₂ (Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) g) = 1 := by
    by_cases hp2 : p = 2
    · subst p
      intro v g hg
      exact hsq _ (hI₂ g hg)
    · exact hur p hp ⟨hp2, hp3⟩
  refine ⟨ψ₁, ψ₂, hc₁, hc₂, hf₁, hf₂, ?_, ?_, hext, hdet⟩
  · intro p hp hp3 v g hg
    exact (hu p hp hp3 g hg).1
  · intro p hp hp3 v g hg
    exact (hu p hp hp3 g hg).2

end HardlyRamified

end ThreeAdicPlan

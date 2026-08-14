# R = T Modularity-Lifting Core — Second Independent Cartography Pass

Bead: hub-lsb1u.11.2 · Date: 2026-08-14 · Sources: /Users/kas/FLT working tree (fork of
ImperialCollegeLondon/FLT, tip `e99f167`, 2026-08-13) + GitHub API for upstream + blueprint
`ch04overview.tex`. Independence: no cartography/ or panel/ material consulted.

---

## 1. Repo inventory (what exists, honestly classified)

### 1.1 FLT/Patching/ — the abstract Taylor–Wiles–Kisin patching argument. SUBSTANTIAL, essentially real.

14 files, ~4,115 lines, **exactly one sorry**.

- `FLT/Patching/REqualsT.lean:86` — **real-Lean, proved**:
  `theorem ker_RtoT_le_nilradical : RingHom.ker RtoT ≤ nilradical R₀`
  This is the payoff theorem: under the patching-system hypotheses (ultrafilter `F` on the index
  set, uniformly bounded ranks, `R∞` a compact noetherian local domain with
  `Module.depth Λ Λ = ringKrullDim Rₒₒ`, quotient identifications `Rᵢ/𝔫 ≃ R₀`, `Mᵢ/𝔫 ≃ M₀`),
  the kernel of `R₀ → T₀` is nilpotent, i.e. R = T after passing to reduced quotients
  (file header: "The final step of the patching argument", REqualsT.lean:13–15).
- `FLT/Patching/System.lean`, `Module.lean`, `Algebra.lean`, `Ultraproduct.lean`,
  `VanishingFilter.lean`, `Over.lean`, `Utils/*` — real-Lean supporting machinery
  (ultraproduct patching à la Andrew Yang's formulation, uniformly-bounded-rank classes,
  adic-topology utilities). Authors: Andrew Yang, Kevin Buzzard.
- `FLT/Patching/Utils/CompactHausdorffRings.lean:42` — **sorry**:
  `Group.subsingleton_of_pow_prime_eq_one` ("a connected compact Hausdorff 𝔽_p-vector space is
  trivial"); docstring notes it needs a Pontryagin/Peter–Weyl-type fact "being worked on at
  `YaelDillies/mean-fourier`". Isolated, size S–M.

Classification: **real-Lean** at the abstract-commutative-algebra level. What Patching/ does NOT
contain: any arithmetic. No Galois groups, no Hecke algebras, no deformation rings are ever
instantiated here — it is a self-contained axiomatized patching formalism awaiting inputs.

### 1.2 FLT/Deformations/ — deformation-theory framework. Framework real, keystones sorried.

17 files, ~2,861 lines, 4 sorries.

- Real-Lean: `Categories.lean` (ProartinianCat), `IsProartinian.lean`, `IsResidueAlgebra.lean`,
  `LiftFunctor.lean` (lift/deformation functors, det condition, unramified/flat/narrow-trace
  condition functors), `RepresentationTheory/GaloisRep.lean` (continuous `GaloisRep K R V` API,
  `toLocal`, Frobenius, base change), `GaloisRepFamily.lean` (compatible families),
  `AbsoluteGaloisGroup.lean`.
- `FLT/Deformations/Representable.lean:38` — **sorry**: `isCorepresentable_deformationFunctor`
  ("de Smit and Lenstra, Proposition 2.3 (1)") — existence of the universal deformation ring for
  absolutely irreducible ρ̄. Size M.
- `FLT/Deformations/Representable.lean:106` — **sorry**: `isCorepresentable_narrowSLiftFunctor` —
  corepresentability of the "narrow S-lift" functor (det = cyclotomic ⊓ unramified outside S∪{ℓ}
  ⊓ narrow trace condition at S ⊓ flat at ℓ — exactly the four bullet points of the blueprint's
  "S-good"). The universal ring `narrowSLiftUniversalRing` (Representable.lean:110) is defined
  by `.choose` on this sorry. Size M–L.
- `FLT/Deformations/LiftFunctor.lean:117` — **sorry**: functoriality `map` field
  ("See e.g. Conrad Theorem 1.6 of CSS"). Size S–M.
- `FLT/Deformations/RepresentationTheory/GaloisRep.lean:385` — comment flags a further
  result deliberately deferred to a sorry-able form.

Classification: **real framework + sorry keystones**. Crucially, `Rᵘⁿⁱᵛ` exists as an object but
nothing is proved about it (no tangent-space dimension, no generators/relations bound, no
`O[[x₁..x_g]]`-presentation).

### 1.3 Hecke side — abstract done, arithmetic Hecke algebra defined, T-valued Galois reps absent.

- `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/{Abstract,Concrete,Local}.lean` —
  **real-Lean, 0 sorries** in the whole AutomorphicForm tree (~4,464 lines). Abstract double-coset
  Hecke operators (`heckeOperator`, commutativity `comm` at Abstract.lean:257), concrete `Tᵥ` on
  quaternionic automorphic forms, and a `HeckeAlgebra` for (D, level).
- `FLT/GaloisRepresentation/Automorphic.lean` — the bridge file. Real statement of
  `GaloisRep.IsAutomorphicOfLevel` (ρ automorphic ⇔ ∃ quaternion algebra D of discriminant 1 and
  Hecke eigensystem `π : HeckeAlgebra → A` with trace ρ(Frobᵥ) = π(Tᵥ), det = cyclotomic;
  lines ~80–95). Two sorries:
  - `Automorphic.lean:100` — quaternion-algebra base-change instance ("Ask Edison?"). Size S.
  - `Automorphic.lean:184` — **cyclic base change for GL₂** (solvable E/F, automorphic-of-level-S
    descent iff). This is the Langlands–Tunnell/Skinner–Wiles analytic input. Size XL.

### 1.4 FLT/GaloisRepresentation/HardlyRamified/ — the Frey-consumption layer. Statements real, proofs absent.

8 files, ~611 lines, 9 sorries — this is where the entire R=T chapter is *consumed* as opaque
statements:

- `Defs.lean` — `IsHardlyRamified` definition, **real, 0 sorries**.
- `Lift.lean:48` — **sorry**: `IsHardlyRamified.lifts` — irreducible mod-ℓ hardly ramified ρ̄
  lifts to a hardly ramified ℓ-adic σ over a finite free ℤ_ℓ-algebra. (Khare–Wintenberger-style
  lifting; blueprint proves it via potential modularity, hence via the modularity lifting theorem.)
- `Family.lean:68` — **sorry**: `mem_isCompatible` — the lift sits in a compatible family which
  is hardly ramified at every odd ℓ. (Potential modularity + Brauer trick of BLGGT; the biggest
  single consumer of R=T.)
- `Threeadic.lean:39`, `ModThree.lean:34` — sorries: 3-adic member is ordinary-flavoured /
  mod-3 reduction is reducible (Langlands–Tunnell-adjacent endgame).
- `Frey.lean:39,41` — sorries: `FreyCurve.torsion_isHardlyRamified`; `Frey.lean:46` —
  `FreyCurve.torsion_not_isIrreducible` ("TODO prove this"; upstream PR #761 targets it
  modulo `knownin1980s`).
- `FLT/Proof.lean:` `B4_proof : B4 := sorry` — the spine's single remaining sorry; B4 ("Frey
  curve E[p] is reducible") ← B5/B6(a,b,c) sketched in comments (Proof.lean:62–75) but B5/B6 are
  not yet even stated as Lean `Prop`s.

### 1.5 Assumptions layer

`FLT/Assumptions/`: `axiom Mazur_statement` (Mazur.lean:105), `axiom Odlyzko_statement`
(Odlyzko.lean:58), and `axiom knownin1980s {P : Prop} : P` (KnownIn1980s.lean:79) — a
deliberate universal escape hatch for pre-1980 mathematics. Any coverage claim must be read
modulo this axiom.

### Coverage estimate for the R=T chapter

By effort weight: abstract patching ~95% done; deformation framework ~70% (framework real,
corepresentability sorried, zero structure theory of R^univ); Hecke/automorphic definitions
~80% but T-valued Galois representations 0%; the modularity lifting theorem itself **0% — not
even stated** (blueprint agrees: "Right now we are very far from even stating this theorem in
Lean", ch04overview.tex:79). **Overall: ~25–30% of the R=T core, concentrated at the two ends
(abstract patching formalism; consumer-facing statement shells) with the arithmetic middle empty.**

---

## 2. Upstream velocity (ImperialCollegeLondon/FLT)

- **Fork is at upstream HEAD.** Local tip `e99f167` (2026-08-13, PR #1164) is upstream main's
  latest commit as of 2026-08-14. We are 0 commits behind.
- Last 30 upstream commits (2026-07-12 → 2026-08-13) are **almost entirely mathlib bumps and CI
  work** (~20 of 30 are `chore: bump mathlib`). Latest commits touching `FLT/Patching` and
  `FLT/Deformations` are all mathlib-bump fixups (168c04a, 734592e, dfe9da7…) — **no substantive
  math has landed in Patching/ or Deformations/ since before mid-July 2026**.
- Substantive motion lives in **open PRs**: #1089 (kbuzzard: ρ irred + hardly ramified ⇒
  ρ|G_{ℚ(ζ_p)} abs irred — a Taylor–Wiles hypothesis), #1083 (Ribet's lemma), #1042 (kbuzzard:
  blueprint chapters toward Gee Prop. 3.24 — deformation-theory roadmap), #761
  (torsion_not_isIrreducible modulo 1980s), #1110/#1105 (local duality / Poitou–Tate nine-term
  complex in KnownIn1980s), #1071 (Moret–Bailly statement), #1155 (GL₀ sorries). Also #1172
  (today's mathlib bump) — the bump cadence is near-daily.
- Reading: upstream is in a **consolidation/infrastructure phase** for this chapter (blueprint
  planning via #1042, hypotheses via #1089, cohomology inputs via #1110/#1105), not a
  landing-big-theorems phase. The 2026 EPSRC TCC course (repo dir `2026_EPSRC_TCC_course`) and
  funding to 2029 imply sustained but deliberate velocity.

---

## 3. Weakest lifting statement the Frey argument consumes

Per `blueprint/src/chapter/ch04overview.tex:66–77` (`\label{modularity_lifting_theorem}`,
marked `\notready`), the Frey argument needs only the **minimal, fixed-determinant, flat
("S-good") lifting theorem**:

> ℓ ≥ 5 prime; F totally real of **even degree** with ℓ **unramified** in F; S a finite set of
> places not dividing ℓ. ρ : G_F → GL₂(𝒪) with det ρ = cyclotomic, unramified outside S∪{ℓ},
> trace ρ(g) = 2 for g ∈ J_v (v ∈ S), and **flat at every v | ℓ**. If ρ̄ is modular of level
> Γ₁(S) and ρ̄|_{G_{F(ζ_ℓ)}} is absolutely irreducible, then ρ is modular of level Γ₁(S).

Weakenings baked in: no ordinary case, no weight variation, fixed cyclotomic determinant, flat
at ℓ (no Fontaine–Laffaille range beyond weight 2), even-degree F (so the quaternion algebra is
totally definite of discriminant 1 — matching `IsAutomorphicOfLevel` in
`FLT/GaloisRepresentation/Automorphic.lean`), ℓ unramified rather than split (blueprint notes
Taylor's meromorphic-continuation paper Thm 3.3 and Gee's Thm 5.2 each come close but not
exactly, ch04overview.tex:81–82). Proof shape (ch04overview.tex:84–91): Skinner–Wiles trick to
the minimal case (needs cyclic base change + multiplicity one + Jacquet–Langlands), then
Taylor–Wiles–Kisin patching. In the Lean tree this theorem's Frey-side shadow is the pair of
sorries `HardlyRamified/Lift.lean:48` and `HardlyRamified/Family.lean:68`; its deformation-side
shell is `narrowSLiftFunctor` (`Deformations/Representable.lean:95–110`), whose four conditions
are exactly the four S-good bullets.

---

## 4. Numbered map of ABSENT pieces (R=T core only)

| # | Absent piece | Size | Where it would live / evidence of absence |
|---|---|---|---|
| A1 | **Lean statement of the modularity lifting theorem** (§3 above). Blueprint: "very far from even stating" (ch04overview.tex:79). Prereqs for the statement mostly now exist (GaloisRep, IsAutomorphicOfLevel, narrowSLiftFunctor), so this is closer than the blueprint text (stale) implies. | M | no file; would join GaloisRepresentation/ |
| A2 | **Galois representation attached to a Hecke eigensystem / into the Hecke algebra** (ρ_π : G_F → GL₂(T_𝔪)), incl. Carayol/local-global. `IsAutomorphicOfLevel` only *compares* a given ρ against eigenvalues; no construction direction exists. | XL | absent; blueprint `\uses{Galois_representation_from_automorphic_representation_on_GL_2_form}` |
| A3 | **R → T surjection and its interface**: T_𝔪 as complete local ring, the map R^univ_S-good → T from A2 + universality. | L | absent |
| A4 | **Corepresentability of deformation/lift functors** (de Smit–Lenstra). | M | sorries `Deformations/Representable.lean:38,106`; `LiftFunctor.lean:117` |
| A5 | **Structure theory of R^univ**: tangent space = H¹_S-good, presentation over 𝒪 with #gens − #rels bounded via global Euler characteristic. Nothing beyond `.choose` exists. | L | absent |
| A6 | **Local deformation-condition theory**: flat local deformation ring at v|ℓ (Fontaine–Laffaille / Kisin flat), its dimension/smoothness; narrow-trace condition ring at v ∈ S. Functors are *defined* (`LiftFunctor.lean`) but zero theorems. | XL | absent |
| A7 | **Taylor–Wiles primes**: existence of TW systems (Chebotarev + H¹ annihilation, uses ρ̄|_{F(ζ_ℓ)} abs irred — upstream PR #1089 is a first step), level-Q_n deformation rings and Hecke modules, `R_∞` as power series over Λ with the depth = Krull-dim hypothesis of `REqualsT.lean:76` discharged. This is the entire bridge from arithmetic into `Patching/System`. | XL | absent; Patching/ has no arithmetic instantiation |
| A8 | **Freeness/finiteness of the Hecke module** M₀ (space of forms) over Λ-levels, `IsPatchingSystem` instance, `Module.UniformlyBoundedRank` verification for the arithmetic modules. | L | absent |
| A9 | **Skinner–Wiles reduction to the minimal case**: cyclic base change (sorry `Automorphic.lean:184`), multiplicity one, Jacquet–Langlands characterisation of the image of base change. Analytic; blueprint calls it the "nontrivial analytic input" (ch04overview.tex:86–88). | XL | sorry + absent |
| A10 | **Jacquet–Langlands** itself (quaternionic ↔ GL₂), needed both for A9 and for the definition of "modular" used. DivisionAlgebra/ has adelic infrastructure but no JL correspondence. | XL | absent |
| A11 | **Potential modularity package**: Moret–Bailly (statement in upstream PR #1071, not merged), auxiliary elliptic curve, induced-from-character modularity (converse theorems), assembling A1 into `HardlyRamified/Lift.lean:48` and `Family.lean:68` (Khare–Wintenberger + BLGGT Brauer trick). | XL | sorries Lift.lean:48, Family.lean:68 |
| A12 | **3-adic endgame**: `Threeadic.lean:39`, `ModThree.lean:34` sorries (hardly-ramified 3-adic reps are extensions of trivial by cyclotomic). | L | sorries |
| A13 | **Frey-curve inputs**: `Frey.lean:39,41,46` (torsion is hardly ramified; irreducibility via Mazur axiom — PR #761 pending). Not R=T proper but on the consumption edge. | M | sorries |
| A14 | **Pontryagin/Peter–Weyl fact** for compact 𝔽_p-vector spaces. Only sorry inside Patching/. Outsourced to `YaelDillies/mean-fourier`. | S–M | sorry `Patching/Utils/CompactHausdorffRings.lean:42` |
| A15 | **B5/B6 as Lean Props** and the B4 ← B5 ← B6 spine (`Proof.lean:62–75` are comments; `B4_proof := sorry`). | M | Proof.lean |

### Dependency edges

- **← hub-lsb1u.10 (Galois reps)**: A2, A3, A11 consume the Galois-representation hub
  (GaloisRep API is real here; the *construction* from automorphic forms is the missing edge).
  A13/A15 consume `EllipticCurve/Torsion.lean` reps of the Frey curve.
- **← hub-lsb1u.7 (Poitou–Tate)**: A5, A6, A7 consume local/global Galois cohomology. The
  blueprint's `\uses` list for the lifting theorem (ch04overview.tex:68–72) names
  `local_galois_coh_dim_two`, `..._top_degree`, `..._poincare`, `..._euler_poincare`,
  `..._finite` — i.e. local Tate duality + local Euler characteristic. Inferred alignment with
  the PT bead's Greenberg–Wiles finding (from blueprint alone): the **global** Euler
  characteristic / Greenberg–Wiles formula is what converts local dimension counts into the
  "#gens = #rels over Λ" and `dim R_∞ = depth Λ` bookkeeping that `Patching/REqualsT.lean:76`
  takes as a *hypothesis* (`H : .some (Module.depth Λ Λ) = ringKrullDim Rₒₒ`) — so PT/Greenberg–
  Wiles is upstream of A5/A7 and is exactly the point where hub-lsb1u.7's output is spent.
  Upstream PRs #1110/#1105 (local duality, nine-term complex, in KnownIn1980s) confirm this
  is being provisioned as an *assumed* 1980s input, not re-proved.
- **Internal**: A1 ← {A2..A11}; A7 ← A5, A6, PT; A8 ← A10 (JL defines the module); A11 ← A1 +
  Moret–Bailly; A12/A13 ← A11; A15 ← A12, A13; `Patching/` (done) is consumed only by A7/A8.

---

## 5. Risks

1. **Duplication risk (highest).** The empty middle (A2–A8) is precisely what kbuzzard's
   blueprint PR #1042 ("toward Gee Prop. 3.24") is planning and what the funded upstream team
   will build; independent construction here would be discarded on sync.
2. **Interface churn.** Deformations/ and Automorphic.lean signatures are young (module-system
   migration, `Slop/` staging namespace, near-daily mathlib bumps 4.32→4.34-rc1 in 4 weeks);
   anything we build against today's `narrowSLiftFunctor` may need rework.
3. **`knownin1980s` opacity.** Coverage numbers can jump discontinuously when hard content is
   routed through the universal axiom; our gap map must track which absences upstream intends
   to axiomatize (A6 local cohomology parts, A10?) vs prove.
4. **Analytic wall.** A9/A10 (base change, JL, multiplicity one) have no formalization
   precedent anywhere; timeline risk concentrates there, not in patching.
5. **Blueprint staleness.** ch04overview.tex:79 ("very far from even stating") predates the
   HardlyRamified/Deformations shells; strategic reads off the blueprint alone now
   underestimate repo state.

## 6. Strategic verdict

**Monitoring + targeted gap-filling; do NOT open an active independent front on the R=T core.**
The abstract patching engine is finished upstream (1 peripheral sorry), the consumer statements
are shelled, and the missing middle (A2–A11) is the upstream PI's own declared next target
(#1042, #1089, #1071). Highest-value fillable gaps that won't collide: A14 (Pontryagin fact —
or upstream the mean-fourier result), A4 (de Smit–Lenstra corepresentability — self-contained
category theory), A13 (Frey hardly-ramified, coordinating with PR #761), and A12. Treat A1
(merely *stating* the lifting theorem in Lean) as the single best-leverage watch item — the
blueprint itself names it "the first target" (ch04overview.tex:112).

**Fork-sync cadence: weekly**, with a PR-watch (not full sync) trigger on any upstream PR
touching `FLT/Patching/`, `FLT/Deformations/`, `FLT/GaloisRepresentation/`, or merging of
#1042/#1089/#1071/#761. Rationale: upstream lands mathlib bumps near-daily (cheap to batch
weekly; falling >2 bumps behind makes rebases painful across 4.3x toolchain jumps), while
substantive math lands in bursts that the PR-watch catches early.

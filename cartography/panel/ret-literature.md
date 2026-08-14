# R=T literature-fidelity panel review — 2026-08-14

1. **Lifting-theorem hypotheses: UNVERIFIED→matches source, but citation label wrong.**
   `ch04overview.tex:38-77` (github.com/ImperialCollegeLondon/FLT/blob/e99f167/blueprint/src/chapter/ch04overview.tex)
   transcribes exactly onto the doc's 8-clause list; `Representable.lean:38-116` mirrors it
   (`3 < l` ⇔ ℓ≥5 prime, OK). Blueprint itself flags no proof source ("I am not entirely
   sure where to find a proof"), citing Taylor Thm 3.3 (stronger: ℓ split not just
   unramified) and Gee Thm 5.2 (stronger: image ⊇ SL₂) as near-misses only — doc's
   `(literature-verify)` caveat is correct, not resolvable from upstream text alone.
   **"Gee's notes Thm 3.24" (task's framing) is a mislabel**: PR #1042 targets Gee's
   *Prop 3.24* (Arizona Winter School 2013 notes / arXiv:2202.05818, a Wiles-product
   Galois-cohomology lemma, i.e. A16 territory), not the modularity lifting theorem —
   unrelated to the ch04 statement being audited. REFUTED (task premise), doc unaffected.

2. **A4 de Smit–Lenstra: VERIFIED source, self-containment UNVERIFIED.** Correct paper:
   de Smit–Lenstra, "Explicit Construction of Universal Deformation Rings," in *Modular
   Forms and FLT* (Springer 1997), Prop 2.3 (free PDF: pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1997a/art.pdf).
   Genuinely commutative-algebra/profinite-groups, no circular FLT dependency visible in
   `Representable.lean`. Could not confirm Prop 2.3(1) is *literally* self-contained
   (didn't read full paper) — mark self-containment UNVERIFIED, citation VERIFIED.

3. **A14 Pontryagin/Peter–Weyl: VERIFIED, but doc's "commutative algebra" tag is wrong.**
   `Patching/Utils/CompactHausdorffRings.lean:24-30` docstring itself states the sorry
   needs "a special case of Pontryagin duality...also a consequence of the Peter-Weyl
   theorem," citing `YaelDillies/mean-fourier` (pushed 2026-08-14, active today —
   coordination note is current, not stale). This is **topological-group theory, not
   commutative algebra** — the task's "same [self-contained commutative algebra]" framing
   for A14 is a category error; content/READY-NOW status otherwise stands.

4. **Velocity claim: CONFIRMED.** Direct GitHub API history filtered to `FLT/Patching`
   and `FLT/Deformations` since 2026-07-01: every commit touching either path is a
   `mathlib bump` chore (6 and 8 commits resp.); zero `feat`/math commits. Repo-wide
   activity in the window is real (Tate curve, PGL₂ classification, base-change) but
   none lands in the R=T core dirs.

5. **Unsourced-import hunt: none found.** Spot-checked `chtopbestiary.tex` (Galois-coh
   axioms) — every `\notready` theorem carries an explicit `\cite{serre-galcoh}`/`\cite{cf}`;
   `KnownIn1980s.lean` grep for bare axioms returned nothing anomalous. No refutation.

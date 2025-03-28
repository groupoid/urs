-- /urs/lib/foundations/universe.urs

-- § Universes: Graded by a monoid 𝒢
-- ↳ Base universes U_α for α ∈ 𝒢, with grade algebra
-- ↳ α represents level and parity (e.g., ℕ × ℤ/2ℤ)

-- Grading monoid 𝒢 (e.g., ℕ × ℤ/2ℤ)
-- ↳ ⊕ : Monoid operation (addition-like)
-- ↳ 𝟘 : Neutral element
-- ↳ Associativity: (α ⊕ β) ⊕ γ = α ⊕ (β ⊕ γ)
-- ↳ Identity: α ⊕ 𝟘 = α = 𝟘 ⊕ α

def 𝒢 : Type := ℕ × ℤ/2ℤ  -- Levels (ℕ) and parity (ℤ/2ℤ: 𝟎 = Bose, 𝟏 = Fermi)
def ⊕ (α β : 𝒢) : 𝒢 := (fst α + fst β, (snd α + snd β) mod 2)
def 𝟘 : 𝒢 := (0, 0)  -- Neutral: level 0, bosonic
def U (α : 𝒢) : Type := Universe α -- Universe formation. U_α : Universe indexed by α ∈ 𝒢 contains types of grade α.
def lift (α β : 𝒢) (δ : 𝒢) (e : U α) : β = α ⊕ δ → U β := λ eq : β = α ⊕ δ, transport (λ x : 𝒢, U x) eq e -- Universe lifting. U_α : U_β if β = α ⊕ δ for some δ ∈ 𝒢, ensures cumulativity: types in U_α lift to U_(α ⊕ δ)
def univ-type (α : 𝒢) : U (α ⊕ (1, 0)) := lift α (α ⊕ (1, 0)) (1, 0) (U α) refl -- § Coherence Conditions 1. Type-in-type formation. U_α : U_(α ⊕ 𝟙) where 𝟙 = (1, 0)
def cumul (α β : 𝒢) (A : U α) (δ : 𝒢) : β = α ⊕ δ → U β := lift α β δ A -- 2. Cumulativity. If A : U_α and α ≤ β (i.e., β = α ⊕ δ), then A : U_β
def prod-rule (α β : 𝒢) (A : U α) (B : A → U β) : U (α ⊕ β) := Π (x : A), B x -- 3. Product formation. Π (x : A) B : U_(α ⊕ β) if A : U_α, B : U_β
def subst-rule (α β : 𝒢) (A : U α) (B : A → U β) (t : A) : U β := B t -- 4. Substitution coherence. If A : U_α, B : A → U_β, and t : A, then B t : U_β
def shift (α δ : 𝒢) (A : U α) : U (α ⊕ δ) := lift α (α ⊕ δ) δ A refl -- 5. Grade shift. Shift grade by δ ∈ 𝒢
def assoc (α β γ : 𝒢) : (α ⊕ β) ⊕ γ = α ⊕ (β ⊕ γ) := refl  -- Arithmetic on ℕ and ℤ/2ℤ is associative -- § Index Algebra Coherence. ⊕ is associative
def ident-left (α : 𝒢) : α ⊕ 𝟘 = α := refl  -- (n + 0, g + 0 mod 2) = (n, g)
def ident-right (α : 𝒢) : 𝟘 ⊕ α = α := refl  -- (0 + n, 0 + g mod 2) = (n, g)

def U₀₀ : Type := U (0, 0)  -- Bosonic level 0
def U₁₀ : Type := U (1, 0)  -- Bosonic level 1
def U₀₁ : Type := U (0, 1)  -- Fermionic level 0
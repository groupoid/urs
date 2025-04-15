module supergeometry where

open import graded

-- Graded Universes
def Grade : Set := {0, 1}
def U (i : Nat) (g : Grade) : Type := Uᵢ^g
def U₀^g (g : Grade) : U 1 g := U 0 g
def grade-sum (g₁ g₂ : Grade) : Grade := (g₁ + g₂) mod 2

-- Graded Tensor Product
def tensor (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) : U i (grade-sum g₁ g₂) := A ⊗ B
def pair-tensor (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) (a : A) (b : B) : tensor i g₁ g₂ A B := a ⊗ b
def tensor-comm (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) (a : A) (b : B) : Path (A ⊗ B) (a ⊗ b) ((-1)^(g₁ * g₂) * (b ⊗ a)) := idp (A ⊗ B) (a ⊗ b)
def proj-tensor₁ (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) (p : A ⊗ B) : A := p.1
def proj-tensor₂ (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) (p : A ⊗ B) : B := p.2

-- Fermionic Unit
def FermionUnit : U 0 1
def nilpotent (θ : FermionUnit) : Path FermionUnit (θ · θ) 0 := idp FermionUnit 0
def anticommutative (θ₁ θ₂ : FermionUnit)
  : Path (tensor 0 1 1 FermionUnit FermionUnit)
         (pair-tensor 0 1 1 FermionUnit FermionUnit θ₁ θ₂)
         ((-1)^(1 * 1) * (pair-tensor 0 1 1 FermionUnit FermionUnit θ₂ θ₁))
  := tensor-comm 0 1 1 FermionUnit FermionUnit θ₁ θ₂

-- FermionUnit Eliminators
def ind-fermion (P : FermionUnit → U i 1) (f : Π (θ : FermionUnit) → P (θ)) (x : FermionUnit) : P x
def ind-fermion-β (P : FermionUnit → U i 1) (f : Π (θ : FermionUnit) → P (θ)) (θ : FermionUnit) : Path (P θ) (ind-fermion P f θ) (f θ) := idp (P θ) (f θ)
def ind-fermion-nil (P : FermionUnit → U i 1) (f : Π (θ : FermionUnit) → P (θ)) (θ : FermionUnit) : Path (P 0) (ind-fermion P f (θ · θ)) (ind-fermion P f 0) := nilpotent θ

def rec-fermion (B : U i 1) (b : B) (b₀ : B) (x : FermionUnit) : B
def rec-fermion-β (B : U i 1) (b : B) (b₀ : B) (θ : FermionUnit) : Path B (rec-fermion B b b₀ θ) b := idp B b
def rec-fermion-β-zero (B : U i 1) (b : B) (b₀ : B) : Path B (rec-fermion B b b₀ 0) b₀ := idp B b₀
def rec-fermion-nil (B : U i 1) (b : B) (b₀ : B) (θ : FermionUnit) : Path B (rec-fermion B b b₀ (θ · θ)) b₀ := nilpotent θ

-- Superspace and Coordinates
def SuperSpace : Set := Nat × Nat
def Grassmann^n (n : Nat) : U 0 1 := Vec FermionUnit n
def BosonicCoord (m : Nat) : U 0 0 := Vec ℝ m
def FermionicCoord (n : Nat) : U 0 1 := Grassmann^n n
def ℝ^{m|n} (mn : SuperSpace) : U 0 0 := let (m, n) := mn in tensor 0 0 1 (BosonicCoord m) (FermionicCoord n)
def superpoint (mn : SuperSpace) (x : BosonicCoord mn.1) (θ : FermionicCoord mn.2) : ℝ^{m|n} mn
 := pair-tensor 0 0 1 (BosonicCoord mn.1) (FermionicCoord mn.2) x θ
def ℝ^{1|1} : U 0 0 := ℝ^{ (1, 1) }

-- Super-Forms
def Ω^{p|q} (mn : SuperSpace) (X : ℝ^{m|n} mn) (p q : Nat) : U 0 (p + q mod 2)
  := tensor 0 p q (Ω^p(X.1)) (Ω^q(X.2))
def dx (mn : SuperSpace) (X : ℝ^{m|n} mn) (i : Fin mn.1) : Ω^{1|0} mn X 1 0 := d (X.1.i)
def dθ (mn : SuperSpace) (X : ℝ^{m|n} mn) (j : Fin mn.2) : Ω^{0|1} mn X 0 1 := d (X.2.j)
def wedge-super (mn : SuperSpace) (X : ℝ^{m|n} mn) (p1 q1 p2 q2 : Nat)
  (ω : Ω^{p1|q1} mn X p1 q1) (η : Ω^{p2|q2} mn X p2 q2)
  : Ω^{p1+p2|q1+q2} mn X (p1+p2) (q1+q2)
  := tensor 0 (p1 + q1 mod 2) (p2 + q2 mod 2) _ _ ω η

-- Bosonic Exterior Derivative
def d-bosonic (m : Nat) (X : BosonicCoord m) (p : Nat) (ω_b : Ω^p(X)) : Ω^{p+1}(X)
 := λ (x : X) → Σ (i : Fin m) → (∂_i ω_b x) ∧ dx i
 where
   ∂_i : Ω^p(X) → (X → ℝ)  -- Partial derivative
   ∧ : ℝ → Ω^1(X) → Ω^{p+1}(X)  -- Wedge product

-- Fermionic Exterior Derivative
def d-fermionic (n : Nat) (X : FermionicCoord n) (q : Nat) (ω_f : Ω^q(X)) : Ω^{q+1}(X)
 := λ (θ : X) → Σ (j : Fin n) → (∂_j ω_f θ) ∧ dθ j
 where
   ∂_j : Ω^q(X) → (X → FermionUnit)  -- Berezin derivative
   ∧ : FermionUnit → Ω^1(X) → Ω^{q+1}(X)  -- Wedge product with Koszul signs
   ∧ x dθ j := (-1)^q * (dθ j ∧ x)  -- Sign adjustment

-- Super-Exterior Derivative
def d-super (mn : SuperSpace) (X : ℝ^{m|n} mn) (p q : Nat) (ω : Ω^{p|q} mn X p q)
  : Ω^{p+1|q} mn X (p+1) q + Ω^{p|q+1} mn X p (q+1)
 := let ω_b := proj-tensor₁ 0 p q (Ω^p(X.1)) (Ω^q(X.2)) ω in
    let ω_f := proj-tensor₂ 0 p q (Ω^p(X.1)) (Ω^q(X.2)) ω in
    let dbω := d-bosonic mn.1 X.1 p ω_b in
    let dfω := d-fermionic mn.2 X.2 q ω_f in
    Coproduct
      (tensor 0 (p+1) q (Ω^{p+1}(X.1)) (Ω^q(X.2)) dbω ω_f)
      (tensor 0 p (q+1) (Ω^p(X.1)) (Ω^{q+1}(X.2)) ω_b dfω)

-- Tests

def fermionic-path-via-rec
  (mn : SuperSpace) (X : ℝ^{m|n} mn) (p q : X) (θ : FermionicCoord mn.2)
  : SuperPathFerm mn X p q
  := λ t : [0,1]. pair-tensor 0 0 1 _ _ (p.1)
       (rec-fermion (FermionicCoord mn.2) (p.2 + t · θ) (p.2) (θ.j))

def dθ-via-ind
  (mn : SuperSpace) (X : ℝ^{m|n} mn) (j : Fin mn.2)
  : Ω^{0|1} mn X 0 1
  := ind-fermion
       (λ θ → Ω^{0|1} mn X 0 1)
       (λ θ → d (X.2.j))
       (X.2.j)

def super-em-form : Ω^{1|1} (1, 1) ℝ^{1|1} 1 1
 := let x := ([x] : BosonicCoord 1) in
    let θ := ([θ] : FermionicCoord 1) in
    let dx := dx (1, 1) ℝ^{1|1} 0 in
    let dθ := dθ (1, 1) ℝ^{1|1} 0 in
    wedge-super (1, 1) ℝ^{1|1} 1 0 0 1
      (x · dx)
      (θ · dθ)

def super-em-form-d : Ω^{2|1} (1, 1) ℝ^{1|1} 2 1 + Ω^{1|2} (1, 1) ℝ^{1|1} 1 2
 := d-super (1, 1) ℝ^{1|1} 1 1 super-em-form



module groupoid where

def Grpd (n : Nat) : U (n + 1) := Sh(Δ, Set)ₖₐₙ
def Grpd∞ : U∞ := Grpd ∞

-- Simplex category
def Δ : U₀ := Δ^n  -- Indexed by n : Nat

-- Constructors
def plt-grpd (n : Nat) (X : Grpd n) : Set := Plt(Δ^n, X)
def comp (n : Nat) (X : Grpd n) (g₁ g₂ : plt-grpd n X) (consec : Consecutive g₁ g₂)
  : plt-grpd n X := g₁ ∘ g₂
def fill (n k : Nat) (X : Grpd n) (h : Π (i : Fin n) (i ≠ k), plt-grpd (n-1) X)
  : plt-grpd n X := fill h

-- Eliminators
def homotopy (X : Grpd 1) (g : plt-grpd 1 X) : Path X (source g) (target g) := g
def compose-elim (n : Nat) (X : Grpd n) (g₁ g₂ : plt-grpd n X) (consec : ...)
  : plt-grpd n X := comp n X g₁ g₂ consec

-- Computation rules
def fill-horn (n k : Nat) (X : Grpd n) (h : ...)
  : Path (plt-grpd (n-1) X) (fill n k X h | Λ_k^n) (h k) := idp (plt-grpd (n-1) X) (h k)

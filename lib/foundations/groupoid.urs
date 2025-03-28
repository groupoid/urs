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

-- Test Terms and Lemmas

-- Test 1: Gauge transformation in BG
def BG (G : Set) : Grpd 1 := λ n, if n = 1 then G else if n = 0 then {pt} else {}
def test-gauge (G : Set) (g : G) : plt-grpd 1 (BG G) := g
def test-homotopy (G : Set) (g : G) : Path (BG G) pt pt := homotopy (BG G) (test-gauge G g)

-- Test 2: Kan condition
def test-horn (X : Grpd 2) (h : plt-grpd 1 X) : plt-grpd 2 X := fill 2 1 X (λ i _, if i = 0 then h else h)
def test-fill-horn (X : Grpd 2) (h : plt-grpd 1 X)
  : Path (plt-grpd 1 X) (fill 2 1 X (λ i _, if i = 0 then h else h) | Λ_1^2) h := fill-horn 2 1 X _

-- Lemma: Gauge equivalence (Page 8)
def gauge-eq (X Y : Grpd∞) (φ : Maps X Y) (φ' : Maps Y X) (g : Maps X X) (h : g = φ' ∘ φ)
  : Path (Grpd∞) X Y := idp _ _  -- homotopy equivalence


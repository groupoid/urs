module supersmooth where

def SupSmthSet : U₁ := Sh(SupCrtSp, Set)

-- Super Cartesian spaces
def SupCrtSp : U₀ := ℝ^(n|q)  -- Indexed by (n, q : Nat)

-- Constructors
def sup-plt (n q : Nat) (X : SupSmthSet) : Set := Plt(ℝ^(n|q), X)
def sup-pair (n q : Nat) (X : SupSmthSet) (φ : plt n X) (ψ : ∧^q (ℝ^q)* → X)
  : sup-plt n q X := (φ, ψ)

-- Eliminators
def bosonic (n q : Nat) (X : SupSmthSet) (φ : sup-plt n q X) : plt n X := φ.1
def fermionic (n q : Nat) (X : SupSmthSet) (φ : sup-plt n q X) : ∧^q (ℝ^q)* → X := φ.2

-- Computation rules
def sup-β₁ (n q : Nat) (X : SupSmthSet) (φ : plt n X) (ψ : ...)
  : Path (plt n X) (bosonic n q X (sup-pair n q X φ ψ)) φ := idp (plt n X) φ
